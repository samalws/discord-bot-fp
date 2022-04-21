{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}

import System.Environment (getEnv)
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.STM (TVar, newTVarIO, readTVarIO, modifyTVar', stateTVar, atomically)
import Control.Monad ((>=>), void, when)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.Reader (ask, local, reader, MonadReader)
import Control.Monad.State (get, gets, put, modify, State, runState, MonadState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, runExceptT, except, withExceptT)
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Control.Monad.Trans.State (StateT, evalStateT)
import Data.Default.Class (Default, def)
import Data.Either.Combinators (whenLeft)
import Data.Maybe (maybe, isNothing, isJust)
import Data.Text (Text, pack, unpack, isPrefixOf)
import Discord (DiscordHandler, discordToken, discordOnEvent, runDiscord, restCall)
import Discord.Types (ChannelId, Event(MessageCreate, Ready), Message, messageChannelId, messageContent, messageAuthor, userIsBot, userId)
import Text.Parsec hiding (State)
import Text.Parsec.Text (Parser)
import Text.Read (readMaybe)
import qualified Control.Concurrent.Event as Ev
import qualified Control.Exception as E
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Discord.Requests as R

-- TODO parse comments, make it so you dont need parens for if or binary operations, make it so typing negative integers (eg -5) works(?)
-- TODO add floats?
-- TODO writing to state variables, @ people, get time, RNG
-- TODO remove unused imports (how?)
-- TODO eventually write bots to a file in order to not have to keep them in memory
-- TODO add allowedList command; make a map from channel to allowed PIDs

startGas = 10000
refuelGas = startGas
gasPushThresh = 2000
sendFnGas = 200
sendFnPause = 500000
binOpGas = 1

type Gas = Int
type PID = Int
data ProcAllowance = Allowed | AllowedNoPrefix deriving Eq
data ProcState m = ProcState { procPID :: PID, procCode :: Code m, procVars :: M.Map Text (TVar (Value m)), channelsAllowed :: M.Map ChannelId ProcAllowance, gasLeft :: Gas, procUpdated :: Ev.Event }
data LamBotState m = LamBotState { procList :: M.Map PID (TVar (ProcState m)), procsAllowed :: M.Map ChannelId (M.Map PID ProcAllowance), maxPID :: Int }

instance Default (LamBotState m) where
  def = LamBotState { procList = M.empty, procsAllowed = M.empty, maxPID = -1 }

type Code m = M.Map Text (Expr m)
data Expr m = ValueExpr (Value m) | ReducibleExpr (m (Expr m))
data Value m = IntVal Int | TextVal Text | BoolVal Bool | IOVal (m (Expr m)) | TupVal (Value m) (Value m) | FnVal (Value m -> m (Expr m)) | VoidVal


class (MonadIO m) => MonadProc m where
  getPID :: m PID
  getAllowed :: ChannelId -> m (Maybe ProcAllowance)
  getGas :: m Gas
  payGas :: Int -> m ()
  pushChanges :: m ()
  descendStmt :: m a -> m a
  getDepth :: m Int
  liftDiscord :: DiscordHandler a -> m a
  botError :: String -> m a

newtype ProcMonad a = ProcMonad { runProcMonad :: ExceptT String (ReaderT (TVar (ProcState ProcMonad),Int) (StateT (ProcState ProcMonad, Gas) DiscordHandler)) a } deriving (Functor, Applicative, Monad, MonadIO, MonadState (ProcState ProcMonad, Int), MonadReader (TVar (ProcState ProcMonad), Int))

instance MonadProc ProcMonad where
  getPID = gets (procPID . fst)
  getAllowed chn = gets (M.lookup chn . channelsAllowed . fst)
  getGas = gets f where f (a,b) = gasLeft a - b
  payGas n = do
    modify $ fmap (+ n)
    g <- gets snd
    when (g > gasPushThresh) pushChanges
  pushChanges = do
    tv <- reader fst
    (state,gasUsed) <- get
    newGas <- liftIO . atomically . stateTVar tv $ (\s -> let g' = gasLeft s - gasUsed in (g', s { gasLeft = g' }))
    liftIO . Ev.signal $ procUpdated state
    newChannels <- liftIO $ channelsAllowed <$> readTVarIO tv
    let state' = state { channelsAllowed = newChannels, gasLeft = newGas }
    put (state', 0)
    when (newGas <= 0) waitForGas
  descendStmt = local $ fmap (+1)
  getDepth = reader snd
  liftDiscord = ProcMonad . lift . lift . lift
  botError s = pushChanges >> ProcMonad (except (Left s))

waitForGas :: ProcMonad ()
waitForGas = do
  ev <- gets (procUpdated . fst)
  liftIO $ Ev.wait ev
  pushChanges

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
runCode s msg pid fn = void . runMaybeT $ do
  fnState <- MaybeT . liftIO $ M.lookup pid . procList <$> readTVarIO s
  fnCode  <- MaybeT . liftIO $ M.lookup fn  . procCode <$> readTVarIO fnState
  let channelVal = IntVal . fromIntegral $ messageChannelId msg
  let authorVal  = IntVal . fromIntegral . userId $ messageAuthor msg
  let contentVal = TextVal $ messageContent msg
  let call a b = ReducibleExpr (appExprSimplF a b)
  stateVal <- liftIO $ readTVarIO fnState
  res <- lift . flip evalStateT (stateVal,0) . flip runReaderT (fnState,0) . runExceptT . runProcMonad . void . runExpr . (`call` contentVal) . (`call` authorVal) . (`call` channelVal) $ fnCode
  case res of
    Left e -> lift $ sendMsgM msg ("Execution of program " <> pack (show pid) <> " failed: " <> pack e)
    _ -> pure ()

appExpr (FnVal f) x = getDepth >>= payGas >> f x
appExpr _ _ = botError "Expected function"

appExprSimplX f x = descendStmt (simplExpr x) >>= appExpr f

appExprSimplF f x = descendStmt (simplExpr f) >>= flip appExpr x

appExprSimplFX f x = do
  f' <- descendStmt (simplExpr f)
  x' <- descendStmt (simplExpr x)
  appExpr f' x'


sepBy2 parser delim = (:) <$> (parser <* delim) <*> sepBy1 parser delim

keywords = ["import","if","then","else"]

-- TODO also allow minus signs
varNameParser = do
  v <- (:) <$> (letter <|> char '_') <*> many (alphaNum <|> char '_')
  if v `elem` keywords then fail "Invalid variable name" else pure v

-- TODO prob add space >> spaces rather than spaces in some of these
ifParser :: (MonadProc m) => Parser (Code m -> Expr m)
ifParser = f <$> g "if" <*> g "then" <*> (string "else" >> spaces >> exprParser) where
  g s = string s >> spaces >> parenParser <* spaces
  f :: (MonadProc m) => (Code m -> Expr m) -> (Code m -> Expr m) -> (Code m -> Expr m) -> (Code m -> Expr m)
  f a b c v = ReducibleExpr $ do
    a' <- descendStmt (simplExpr (a v))
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
  f a b vars = ReducibleExpr $ ValueExpr <$> (TupVal <$> descendStmt (simplExpr (a vars)) <*> descendStmt (simplExpr (b vars)))

parenParser :: (MonadProc m) => Parser (Code m -> Expr m)
parenParser = char '(' >> exprParser <* char ')'

lamParser :: (MonadProc m) => Parser (Code m -> Expr m)
lamParser = f <$> (char '\\' >> varNameParser) <*> (spaces >> exprParser) where
  f :: (MonadProc m) => String -> (Code m -> Expr m) -> Code m -> Expr m
  f var expr vars = ValueExpr $ FnVal (\val -> pure $ expr (M.insert (pack var) (ValueExpr val) vars))

binOpParser :: (MonadProc m) => Parser (Code m -> Expr m)
binOpParser = f <$> (try appParser <|> subAppParser) <*> (spaces >> opParser <* spaces) <*> try exprParser where
  f a o b vars = ReducibleExpr $ do
    a' <- descendStmt . simplExpr $ a vars
    b' <- descendStmt . simplExpr $ b vars
    payGas binOpGas
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

importParser :: Parser PID
importParser = string "import" >> space >> spaces >> (read <$> many1 digit) <* spaces <* char ';'

fnParser' :: (MonadProc mp, Monad mi) => Parser (mi [(Text, Code mp -> Expr mp)])
fnParser' = pure . (:[]) <$> fnParser

importParser' :: (MonadProc mp, Monad mi) => (PID -> mi (Code mp)) -> Parser (mi [(Text, Code mp -> Expr mp)])
importParser' grabCode = f <$> importParser where
  f pid = g <$> grabCode pid
  g code = fmap const <$> M.toList code

trySepBy p delim = try ((:) <$> (p <* delim) <*> trySepBy p delim) <|> pure []

codeParser :: (MonadProc mp, Monad mi) => (PID -> mi (Code mp)) -> Parser (mi (Code mp))
codeParser grabCode = fmap (f . M.fromList . ((fmap const <$> codeDefaults) ++) . concat) . sequence <$> trySepBy (try fnParser' <|> try (importParser' grabCode)) spaces where
  f :: M.Map Text (Code mp -> Expr mp) -> M.Map Text (Expr mp)
  f code = let code' = ($ code') <$> code in code'

codeFileParser :: (MonadProc mp, Monad mi) => (PID -> mi (Code mp)) -> Parser (mi (Code mp))
codeFileParser grabCode = spaces >> optional (string "```") >> spaces >> codeParser grabCode <* spaces <* optional (string "```") <* spaces <* eof

parseCode :: (MonadProc mp, Monad mi) => (PID -> mi (Code mp)) -> Text -> Either ParseError (mi (Code mp))
parseCode grabCode = parse (codeFileParser grabCode) "Inputted function"


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
    ("sendMsg", twoArityHelper sendMsgFn),
    ("delayMicroS", oneArityHelper (delayFn 1)),
    ("delayMs", oneArityHelper (delayFn 1000)),
    ("delaySec", oneArityHelper (delayFn 1000000)),
    ("getGas", ValueExpr . IOVal $ payGas 1 >> fmap (ValueExpr . IntVal) getGas),
    ("pass", ValueExpr . IOVal . pure $ ValueExpr VoidVal)
  ] -- TODO getPID, getAllowed

oneArityHelper f = ValueExpr (FnVal f)
twoArityHelper f = ValueExpr (FnVal $ pure . oneArityHelper . f)
threeArityHelper f = ValueExpr (FnVal $ pure . twoArityHelper . f)

substrFn (IntVal a) (IntVal b) (TextVal t) = pure . ValueExpr . TextVal . T.take (b - a) $ T.drop a t
substrFn _ _ _ = botError "Expected int, int, and string"

lenFn (TextVal t) = pure . ValueExpr . IntVal $ T.length t
lenFn _ = botError "Expected string"

sendMsgFn (IntVal c) (TextVal t) = pure . ValueExpr . IOVal $ do
  payGas sendFnGas
  pushChanges
  pid <- getPID
  allowed <- getAllowed (fromIntegral c)
  case allowed of
    Nothing -> pure ()
    Just Allowed -> liftDiscord (sendMsg (fromIntegral c) ("[" <> pack (show pid) <> "] " <> t))
    Just AllowedNoPrefix -> liftDiscord (sendMsg (fromIntegral c) t)
  liftIO (threadDelay sendFnPause)
  pure (ValueExpr . BoolVal $ isJust allowed)
sendMsgFn _ _ = botError "Expected channel ID and string"

delayFn mul (IntVal x) = pure . ValueExpr . IOVal $ payGas 5 >> pushChanges >> liftIO (threadDelay (mul * x)) >> pure (ValueExpr VoidVal)
delayFn _ _ = botError "Expected int"


sendMsg c msg = void . restCall $ R.CreateMessage c msg
sendMsgM m = sendMsg (messageChannelId m)

newBotState :: M.Map ChannelId ProcAllowance -> Code m -> PID -> IO (TVar (ProcState m))
newBotState a c pid = do
  ev <- Ev.new
  newTVarIO $ ProcState { procPID = pid, procCode = c, procVars = M.empty, channelsAllowed = a, gasLeft = startGas, procUpdated = ev }

addBotIO :: M.Map ChannelId ProcAllowance -> Code m -> TVar (LamBotState m) -> IO PID
addBotIO a c s = do
  pid <- atomically . stateTVar s $ (\st -> let pid = maxPID st + 1 in (pid, st { maxPID = pid }))
  botState <- newBotState a c pid
  atomically . modifyTVar' s $ (\st -> st { procList = M.insert pid botState (procList st) })
  pure pid

addStdLib :: String -> TVar (LamBotState ProcMonad) -> IO ()
addStdLib fname state = do
  fileText <- pack <$> readFile fname
  case parseCode (const $ error "stdlib tried to import") fileText of
    Left e -> error $ "Parse error: " <> show e
    Right c -> do
      c' <- c
      pid <- addBotIO M.empty c' state
      putStrLn $ "Added stlib with pid " <> show pid


msgContentHandler :: TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ()
msgContentHandler s m | "_addProc " `isPrefixOf` messageContent m = flip whenLeft (sendMsgM m . pack) =<< runExceptT (do
  c <- withExceptT (("Parse error: " <>) . show) . except $ parseCode getCode (T.drop (length ("_addProc " :: String)) (messageContent m))
  code <- withExceptT (("Couldn't find process with PID " <>) . show) c
  pid <- liftIO $ addBotIO (M.singleton (messageChannelId m) Allowed) code s
  lift . sendMsgM m . pack $ "Created process with ID " <> show pid
  lift $ runCode s m pid "start")
  where
    getCode :: PID -> ExceptT PID DiscordHandler (Code ProcMonad)
    getCode pid = do
      thisProc <- liftIO $ M.lookup pid . procList <$> readTVarIO s
      maybe (except (Left pid)) (liftIO . fmap procCode . readTVarIO) thisProc
msgContentHandler s m | onCmdList (messageContent m) = void . sequence $ ($ m) . ($ s) . snd <$> cmdList
msgContentHandler s m = do
  r <- ask
  ks <- liftIO $ M.keys . procList <$> readTVarIO s
  void . liftIO . sequence $ forkIO . flip runReaderT r . flip (runCode s m) "msg" <$> ks

onCmdList s = any (`isPrefixOf` s) $ fst <$> cmdList

cmdList :: [(Text, TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ())]
cmdList = (f <$> modifyProcessCmds) <> (g <$> readProcessCmds) where
  f (x,y) = (x, runModifyProcessCmdFromList (x,y))
  g (x,y) = (x, runReadProcessCmdFromList (x,y))

modifyProcessCmds :: [(Text, ((Message -> ProcState ProcMonad -> ProcState ProcMonad), (PID -> String), Text))]
modifyProcessCmds = [
    ("_refuel ", ((\_ sv -> sv { gasLeft = refuelGas }), (\pid -> "Refueled process " <> show pid <> "'s gas to " <> show refuelGas), "refueled")),
    ("_allow ", ((\m sv -> sv { channelsAllowed = M.insert (messageChannelId m) Allowed (channelsAllowed sv) }), (\pid -> "Allowed process " <> show pid <> " in this channel"), "allowed")),
    ("_allowNoPrefix ", ((\m sv -> sv { channelsAllowed = M.insert (messageChannelId m) AllowedNoPrefix (channelsAllowed sv) }), (\pid -> "Allowed process " <> show pid <> " in this channel without a [" <> show pid <> "] prefix"), "allowed")),
    ("_ban ", ((\m sv -> sv { channelsAllowed = M.delete (messageChannelId m) (channelsAllowed sv) }), (\pid -> "Banned process " <> show pid <> " from this channel"), "banned"))
  ]

readProcessCmds :: [(Text, Message -> ProcState ProcMonad -> String)]
readProcessCmds = [
    ("_gas ",(\_ sv -> "Process " <> show (procPID sv) <> " has " <> show (gasLeft sv) <> " gas")),
    ("_allowed ",(\m sv -> "Process " <> show (procPID sv) <> genAllowedMsg (procPID sv) (M.lookup (messageChannelId m) (channelsAllowed sv))))
  ]
  where
    genAllowedMsg _ Nothing = " is banned in this channel"
    genAllowedMsg _ (Just Allowed) = " is allowed in this channel"
    genAllowedMsg pid (Just AllowedNoPrefix) = " is allowed in this channel without the [" <> show pid <> "] prefix"

runModifyProcessCmdFromList (pre,(f,msgGen,fnCall)) s m = when (pre `isPrefixOf` messageContent m) (runModifyProcessCmd (T.length pre) f msgGen fnCall s m)

runReadProcessCmdFromList (pre,f) s m = when (pre `isPrefixOf` messageContent m) (runReadProcessCmd (T.length pre) f s m)

runCmd :: Int -> (TVar (ProcState ProcMonad) -> PID -> TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ()) -> TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ()
runCmd preLen f s m = flip when (sendMsgM m "Couldn't find a process with that PID") . isNothing =<< runMaybeT (do
  -- TODO use hoistMaybe instead of MaybeT . pure; I can't get the import to work
  pid <- MaybeT . pure . readMaybe . unpack $ T.drop preLen (messageContent m)
  procState <- MaybeT . liftIO $ M.lookup pid . procList <$> readTVarIO s
  lift $ f procState pid s m)

runModifyProcessCmd :: Int -> (Message -> ProcState ProcMonad -> ProcState ProcMonad) -> (PID -> String) -> Text -> TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ()
runModifyProcessCmd preLen f msgGen fnCall = runCmd preLen $ (\procState pid s m -> do
  liftIO . atomically $ modifyTVar' procState (f m)
  liftIO $ (procUpdated <$> readTVarIO procState) >>= Ev.signal
  sendMsgM m . pack $ msgGen pid
  r <- ask
  void . liftIO . flip runReaderT r $ runCode s m pid fnCall)

runReadProcessCmd :: Int -> (Message -> ProcState ProcMonad -> String) -> TVar (LamBotState ProcMonad) -> Message -> DiscordHandler ()
runReadProcessCmd preLen f = runCmd preLen $ (\procState pid s m -> liftIO (f m <$> readTVarIO procState) >>= sendMsgM m . pack)

eventHandler :: TVar (LamBotState ProcMonad) -> Event -> DiscordHandler ()
eventHandler s (MessageCreate m) | not (userIsBot (messageAuthor m)) = msgContentHandler s m
eventHandler s (Ready {}) = liftIO $ putStrLn "Bot is online"
eventHandler _ _ = pure ()

main = do
  tok <- getEnv "token"
  state <- newTVarIO (def :: LamBotState ProcMonad)
  addStdLib "stdLib" state
  otp <- runDiscord $ def {
    discordToken = "Bot " <> pack tok,
    discordOnEvent = eventHandler state
  }
  putStrLn $ unpack otp
