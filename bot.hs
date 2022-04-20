{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}

import System.Environment (getEnv)
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad ((>=>), void)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.State (get, put, State, runState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (runReaderT, ask)
import Data.Default.Class (Default)
import Data.Maybe (maybe)
import Data.Text (Text, pack, unpack, isPrefixOf)
import Discord
import Discord.Types
import Text.Parsec hiding (State)
import Text.Parsec.Text
import qualified Control.Exception as E
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Discord.Requests as R

-- TODO parse comments
-- TODO make it so you dont need parens for if or binary operations
-- TODO import other procs; do standard library by having "import 0"
-- TODO make it so typing negative integers (eg -5) works(?)
-- TODO add floats?
-- TODO writing to state variables, @ people, get time, RNG

type Gas = Int
type PID = Int
data ProcAllowance = Allowed | AllowedNoPrefix deriving Eq
data ProcState m = ProcState { procCode :: Code m, procVars :: M.Map Text (TVar (Value m)), channelsAllowed :: M.Map ChannelId ProcAllowance }
data LamBotState m = LamBotState { procList :: M.Map PID (ProcState m), procsAllowed :: M.Map ChannelId (M.Map PID ProcAllowance), maxPID :: Int }

instance Default (ProcState m) where
  def = ProcState { procCode = M.empty, procVars = M.empty, channelsAllowed = M.empty }

instance Default (LamBotState m) where
  def = LamBotState { procList = M.empty, procsAllowed = M.empty, maxPID = 0 }

type Code m = M.Map Text (Expr m)
data Expr m = ValueExpr (Value m) | ReducibleExpr (m (Expr m))
data Value m = IntVal Int | TextVal Text | BoolVal Bool | IOVal (m (Expr m)) | TupVal (Value m) (Value m) | FnVal (Value m -> m (Expr m)) | VoidVal


type ProcMonad = ExceptT String DiscordHandler

class (MonadIO m) => MonadProc m where
  payGas :: Int -> m ()
  getGas :: m Int
  liftDiscord :: DiscordHandler a -> m a
  botError :: String -> m a

instance MonadProc (ExceptT String DiscordHandler) where
  payGas n = pure () -- TODO
  getGas = pure 0 -- TODO
  liftDiscord = lift
  botError s = except (Left s)

simplExpr :: (MonadProc m) => Expr m -> m (Value m)
simplExpr (ValueExpr x) = pure x
simplExpr (ReducibleExpr x) = x >>= simplExpr

runExpr :: (MonadProc m) => Expr m -> m (Expr m)
runExpr e = do
  e' <- simplExpr e
  case e' of
    IOVal x -> x
    _ -> botError "Expected IO"

runCode :: TVar (LamBotState ProcMonad) -> Message -> PID -> Text -> DiscordHandler ()
runCode s msg pid fn = do
  fnCode <- liftIO . atomically $ (M.lookup pid . procList >=> M.lookup fn . procCode) <$> readTVar s
  let channelVal = IntVal . fromIntegral $ messageChannelId msg
  let authorVal  = IntVal . fromIntegral . userId $ messageAuthor msg
  let contentVal = TextVal $ messageContent msg
  let call a b = ReducibleExpr (appExprSimplF a b)
  res <- runExceptT $ maybe (pure ()) (void . runExpr . (`call` contentVal) . (`call` authorVal) . (`call` channelVal)) fnCode
  case res of
    Left e -> sendMsgM msg ("Execution of program " <> pack (show pid) <> " failed: " <> pack e)
    _ -> pure ()

appExpr (FnVal f) x = payGas 1 >> f x
appExpr _ _ = botError "Expected function"

appExprSimplX f x = simplExpr x >>= appExpr f

appExprSimplF f x = simplExpr f >>= flip appExpr x

appExprSimplFX f x = do
  f' <- simplExpr f
  x' <- simplExpr x
  appExpr f' x'


sepBy2 parser delim = (:) <$> (parser <* delim) <*> sepBy1 parser delim

keywords = ["if","then","else"]

varNameParser = do
  v <- (:) <$> letter <*> many alphaNum
  if v `elem` keywords then fail "Invalid variable name" else pure v

ifParser :: (MonadProc m) => Parser (Code m -> Expr m)
ifParser = f <$> g "if" <*> g "then" <*> (string "else" >> spaces >> exprParser) where
  g s = string s >> spaces >> parenParser <* spaces
  f :: (MonadProc m) => (Code m -> Expr m) -> (Code m -> Expr m) -> (Code m -> Expr m) -> (Code m -> Expr m)
  f a b c v = ReducibleExpr $ do
    a' <- simplExpr (a v)
    case a' of
      (BoolVal True) -> pure (b v)
      (BoolVal False) -> pure (c v)
      _ -> botError "Expected boolean"

varParser :: (MonadProc m) => Parser (Code m -> Expr m)
varParser = f <$> varNameParser where
  f varName vars = case M.lookup (pack varName) vars of
    Nothing -> ReducibleExpr (botError ("Undefined variable " <> varName))
    Just x -> x

intParser :: Parser (Code m -> Expr m)
intParser = const . ValueExpr . IntVal . read <$> many1 digit

textParser :: Parser (Code m -> Expr m)
textParser = const . ValueExpr . TextVal . pack <$> (char '"' >> many (noneOf ['"']) <* char '"') -- TODO escape characters

voidParser :: (MonadProc m) => Parser (Code m -> Expr m)
voidParser = char '(' >> space >> char ')' >> pure (const (ValueExpr VoidVal))

tupParser :: (MonadProc m) => Parser (Code m -> Expr m)
tupParser = f <$> (char '(' >> exprParser <* spaces <* char ',') <*> (spaces >> exprParser <* char ')') where
  f a b vars = ReducibleExpr $ ValueExpr <$> (TupVal <$> simplExpr (a vars) <*> simplExpr (b vars))

parenParser :: (MonadProc m) => Parser (Code m -> Expr m)
parenParser = char '(' >> exprParser <* char ')'

lamParser :: (MonadProc m) => Parser (Code m -> Expr m)
lamParser = f <$> (char '\\' >> varNameParser) <*> (spaces >> exprParser) where
  f :: (MonadProc m) => String -> (Code m -> Expr m) -> Code m -> Expr m
  f var expr vars = ValueExpr $ FnVal (\val -> pure $ expr (M.insert (pack var) (ValueExpr val) vars))

binOpParser :: (MonadProc m) => Parser (Code m -> Expr m)
binOpParser = f <$> (try appParser <|> subAppParser) <*> (spaces >> opParser <* spaces) <*> try exprParser where
  f a o b vars = ReducibleExpr $ do
    a' <- simplExpr $ a vars
    b' <- simplExpr $ b vars
    payGas 1
    o a' b'

  opParser :: (MonadProc m) => Parser (Value m -> Value m -> m (Expr m))
  opParser = _fold (<|>) ((\(op,fn) -> try (string op >> pure fn)) <$> ops)

  _fold f [a] = a
  _fold f (a:r) = f a (_fold f r)

appParser :: (MonadProc m) => Parser (Code m -> Expr m)
appParser = f <$> sepBy2 subAppParser spaces where
  f [a,b] vars = ReducibleExpr $ appExprSimplFX (a vars) (b vars)
  f (a:b:r) vars = f (f [a,b]:r) vars

subAppParser :: (MonadProc m) => Parser (Code m -> Expr m)
subAppParser = varParser <|> intParser <|> textParser <|> try tupParser <|> parenParser

exprParser :: (MonadProc m) => Parser (Code m -> Expr m)
exprParser = lamParser <|> try ifParser <|> try binOpParser <|> try appParser <|> subAppParser

fnParser :: (MonadProc m) => Parser (Text, Code m -> Expr m)
fnParser = (,) <$> (pack <$> varNameParser) <*> (spaces >> char '=' >> spaces >> exprParser <* char ';')

trySepBy p delim = try ((:) <$> (p <* delim) <*> trySepBy p delim) <|> pure []

codeParser :: (MonadProc m) => Parser (Code m)
codeParser = f . M.fromList . ((fmap const <$> codeDefaults) ++) <$> trySepBy (try fnParser) spaces where
  f :: M.Map Text (Code m -> Expr m) -> M.Map Text (Expr m)
  f code = let code' = ($ code') <$> code in code'

codeFileParser :: (MonadProc m) => Parser (Code m)
codeFileParser = spaces >> optional (string "```") >> spaces >> codeParser <* spaces <* optional (string "```") <* spaces <* eof

parseCode :: (MonadProc m) => Text -> Either ParseError (Code m)
parseCode = parse codeFileParser "Inputted function"


ops :: (MonadProc m) => [(String, Value m -> Value m -> m (Expr m))]
ops = otherOps ++ numOps ++ numBoolOps

otherOps :: (MonadProc m) => [(String, Value m -> Value m -> m (Expr m))]
otherOps = [("+",addOp),(">>",bindOp),("&",andOp),("|",orOp),("==",eqOp)]

numOps :: (MonadProc m) => [(String, Value m -> Value m -> m (Expr m))]
numOps = fmap numOp <$> [("-",(-)),("*",(*)),("/",div),("%",mod),("^",(^))]

numBoolOps :: (MonadProc m) => [(String, Value m -> Value m -> m (Expr m))]
numBoolOps = fmap numBoolOp <$> [(">=",(>=)),("<=",(<=)),(">",(>)),("<",(<))]

numOp op (IntVal a) (IntVal b) = pure . ValueExpr . IntVal $ a `op` b
numOp _ _ _ = botError "Expected number"

numBoolOp op (IntVal a) (IntVal b) = pure . ValueExpr . BoolVal $ a `op` b
numBoolOp _ _ _ = botError "Expected number"

addOp (IntVal a) (IntVal b) = pure . ValueExpr . IntVal $ a + b
addOp (TextVal a) (TextVal b) = pure . ValueExpr . TextVal $ a <> b
addOp _ _ = botError "Expected number or string"

bindOp (IOVal a) b = pure . ValueExpr . IOVal $ a >>= appExprSimplX b >>= runExpr
bindOp _ _ = botError "Expected IO and function"

andOp (BoolVal a) (BoolVal b) = pure . ValueExpr . BoolVal $ a && b
andOp _ _ = botError "Expected boolean"

orOp (BoolVal a) (BoolVal b) = pure . ValueExpr . BoolVal $ a || b
orOp _ _ = botError "Expected boolean"

eqOp (IntVal  a) (IntVal  b) = pure . ValueExpr . BoolVal $ a == b
eqOp (TextVal a) (TextVal b) = pure . ValueExpr . BoolVal $ a == b
eqOp (BoolVal a) (BoolVal b) = pure . ValueExpr . BoolVal $ a == b
eqOp _ _ = botError "Expected number, string, or boolean"


codeDefaults :: (MonadProc m) => [(Text, Expr m)]
codeDefaults = [
    ("false", ValueExpr . BoolVal $ False),
    ("true",  ValueExpr . BoolVal $ True),
    ("substr", threeArityHelper substrFn),
    ("len", oneArityHelper lenFn),
    ("log", oneArityHelper logFn),
    ("sendMsg", twoArityHelper sendFn),
    ("delayMicroS", oneArityHelper delayMicroSFn),
    ("delayMs", oneArityHelper delayMsFn),
    ("delaySec", oneArityHelper delaySecFn),
    ("getGas", ValueExpr . IOVal $ fmap (ValueExpr . IntVal) getGas),
    ("pass", ValueExpr . IOVal . pure $ ValueExpr VoidVal)
  ]

oneArityHelper f = ValueExpr (FnVal f)
twoArityHelper f = ValueExpr (FnVal $ pure . oneArityHelper . f)
threeArityHelper f = ValueExpr (FnVal $ pure . twoArityHelper . f)

substrFn (IntVal a) (IntVal b) (TextVal t) = pure . ValueExpr . TextVal . T.take (b - a) $ T.drop a t
substrFn _ _ _ = botError "Expected int, int, and string"

lenFn (TextVal t) = pure . ValueExpr . IntVal $ T.length t
lenFn _ = botError "Expected string"

logFn (TextVal t) = pure . ValueExpr . IOVal $ (liftIO . putStrLn $ unpack t) >> pure (ValueExpr VoidVal)
logFn _ = botError "Expected string"

sendFn (IntVal c) (TextVal t) = pure . ValueExpr . IOVal $ liftDiscord (sendMsg (fromIntegral c) t) >> liftIO (threadDelay 500000) >> pure (ValueExpr VoidVal)
sendFn _ _ = botError "Expected channel ID and string"

delayMicroSFn (IntVal x) = pure . ValueExpr . IOVal $ liftIO (threadDelay x) >> pure (ValueExpr VoidVal)
delayMicroSFn _ = botError "Expected int"

delayMsFn (IntVal x) = pure . ValueExpr . IOVal $ liftIO (threadDelay (x * 1000)) >> pure (ValueExpr VoidVal)
delayMsFn _ = botError "Expected int"

delaySecFn (IntVal x) = pure . ValueExpr . IOVal $ liftIO (threadDelay (x * 1000000)) >> pure (ValueExpr VoidVal)
delaySecFn _ = botError "Expected int"

sendMsg c msg = restCall (R.CreateMessage c msg) >> pure ()
sendMsgM m = sendMsg (messageChannelId m)

addBot :: Code m -> State (LamBotState m) PID
addBot c = do
  s <- get
  let pid = maxPID s + 1
  put $ s {
    procList = M.insert pid (def { procCode = c }) (procList s),
    maxPID = pid
  }
  return pid

-- TODO permissions system
msgContentHandler s m | "_addProc " `isPrefixOf` messageContent m = do
  case parseCode (T.drop (length ("_addProc " :: String)) (messageContent m)) of
    Left e -> sendMsgM m $ pack $ "Parse error: " <> show e
    Right c -> do
      pid <- liftIO . atomically . stateTVar s . runState $ addBot c
      sendMsgM m $ pack $ "Created process with ID " <> show pid
      -- TODO enable bot in this channel
      runCode s m pid "start"
msgContentHandler s m = do
  r <- ask
  ks <- liftIO . atomically $ M.keys . procList <$> readTVar s
  liftIO . sequence $ forkIO . flip runReaderT r . flip (runCode s m) "msg" <$> ks
  pure ()

eventHandler s (MessageCreate m) | not (userIsBot (messageAuthor m)) = msgContentHandler s m
eventHandler s (Ready {}) = liftIO $ putStrLn "Bot is online"
eventHandler _ _ = pure ()

main = do
  tok <- getEnv "token"
  state <- newTVarIO (def :: LamBotState ProcMonad)
  otp <- runDiscord $ def {
    discordToken = "Bot " <> pack tok,
    discordOnEvent = eventHandler state
  }
  putStrLn $ unpack otp
