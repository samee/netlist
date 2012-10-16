-- Ideally, this is how I wanted things to be
-- theAwsomeCircuit :: Lists of Pairs of Maybes of Net*# variables
--                  -> NetWriter (Lists of Pairs of Maybes of Net*# variables)
--
-- main = do
--   (x,y,z) <- whipOutOneLinersToConjureUp500MDataStructures
--   outputs <- burnCircuit fileHandle $ theAwesomeCircuit x y z
--   gcilShow outputs
--
-- Problems:
-- Nobody specified which input comes from which party here ...
-- NetWriter is not a transformer on IO, so I can't really have x,y,z hanging
--   around in IO if they are plain NetList variables
-- I don't really want to "leak" outputs after circuits have been burned
--
-- Solutions
-- Leak fix: don't fix it. It's not your job to solve global dumbness
-- burnCircuit :: handle -> (NetWriter(),IO()) -> IO ()
-- gcilShow = ultimate sed script input
--   This guy needs to send its OutputBits to burnCircuit,
--   and formatting into some new file.
-- gcilShow :: GcilShow a => templateName -> a -> (IO(),NetWriter())
--
-- So now the output part looks like
-- burnCircuit fileHandle $ theAwesomeCircuit x y z >>= gcilShow tmpl
--
-- Now for the inputs:
-- Things like gcilUInt and gcilBool will wrap newBits
-- gcilUInt :: party -> width -> WriterT [InputSpec] NetWriter NetUInt
-- testUInt :: party -> width -> value -> WriterT [InputSpec] NetWriter NetUInt
--
-- appSpecificCompile x y z = [GcilInstr]
--
-- shut up and NetList.conjureVar, and netWriter init state from NetList.netList
--
-- main = do
--   friendlyInputs <- getStdRandom randomlyGenerateThose500MDataStructures
--   burnTestCase "casename" $ appSpecificCompile friendlyInputs
--     
-- Writing appSpecificCompile:
--   gcilList $ do v <- testInt 
--                 v2 <- testInt 
--                 -- no more new variable declarations below this
--                 outputs <- liftNet $ awesomeCircuit v v2
--                 eq <- ignoreAndsUsed $ liftNet $ checkCircuit outputs
--                 liftNet $ newOutput =<< bitify eq
-- 
-- gcilShow for output has to be shelved for now. Some other day

module Circuit.NetList.Gcil
( gcilList
, InputParty(..)
, testInt
, liftNet
, gcilOutBits
, ignoreAndsUsed
, burnTestCase
) where

import Control.Monad.State.Strict
import Control.Monad.Writer
import Data.IORef
import System.IO
import Circuit.NetList

data InputParty = ServerSide | ClientSide deriving Eq
data InputSpec = InputSpec { party :: InputParty
                           , inputWidth :: Int
                           , varId :: Int
                           , testValue :: Int
                           }

data GcilInstr = InputInstr InputSpec
               | CalcInstr NetInstr
               | StartIgnoreStats
               | EndIgnoreStats

burnTestCase :: String -> [GcilInstr] -> IO ()
burnTestCase caseName bytecode = do
  counting <- newIORef True
  andCount <- newIORef 0
  writeCaseFiles caseName $ \cktFile serverInfile clientInfile ->
    forM_ bytecode $ \bc -> case bc of
      InputInstr input -> do
        writeInValue serverInfile clientInfile input
        writeInSpec cktFile input
      CalcInstr netinstr -> do compileNetInstr cktFile netinstr
                               c <- readIORef counting
                               when c $ 
                                 modifyIORef' andCount (+ andCost netinstr)
      StartIgnoreStats   -> writeIORef counting False
      EndIgnoreStats     -> writeIORef counting True
  ac <- readIORef andCount
  putStrLn $ caseName ++ " " ++ show ac

type GcilMonad = WriterT [GcilInstr] (State Int)
gcilList :: GcilMonad a -> [GcilInstr]
gcilList ckt = evalState (execWriterT ckt) 1

gcilOutBits x = liftNet $ newOutput =<< bitify x

gcilTestInput party width value = do id <- state (\id -> (id,id+1))
                                     let l = InputSpec party width id value
                                     tell [InputInstr l]
                                     return l

toNet v = conjureBits (inputWidth v) (varId v)

testInt :: NetInt i => InputParty -> Int -> Int -> GcilMonad i
testInt party width value 
  = liftM (intFromBits.toNet) $ gcilTestInput party width value

liftNet :: NetWriter a -> GcilMonad a
liftNet nw = do initId <- lift get
                let ((result,endId),nl) = netList addend initId
                put endId
                tell $ map CalcInstr nl
                return result
  where addend = do r <- nw
                    endId <- nextBitId
                    return (r,endId)

ignoreAndsUsed mr = do tell [StartIgnoreStats]
                       r <- mr
                       tell [EndIgnoreStats]
                       return r

andCost (OutputBits _) = 0
andCost (AssignResult _ op) = opcodeAndCost op

-- Add, Sub and Neg should be a gate cheaper, but currently isn't
opcodeAndCost (BinOp BitXor _ _) = 0
opcodeAndCost (BinOp BitEq x _) = bitWidth x - 1
opcodeAndCost (BinOp _ x _) = bitWidth x
opcodeAndCost (UnOp BitNeg x) = bitWidth x
opcodeAndCost (UnOp BitAny x) = bitWidth x - 1
opcodeAndCost (UnOp BitParityOdd _) = 0
opcodeAndCost (UnOp BitNot _) = 0
opcodeAndCost (ConcatOp _) = 0
opcodeAndCost (SelectOp _ _ _) = 0
opcodeAndCost (ExtendOp _ _ _) = 0

idName v = 't':show v
inName = idName.varId

writeInValue sin cin v = hPutStrLn h $ inName v ++ " " ++ show (testValue v)
  where h = if party v == ServerSide then sin else cin

writeInSpec cktfile v = hPutStrLn cktfile 
                      $ ".input "++inName v++" "++ps++" "++ws
  where ps = if party v == ServerSide then "2" else "1"
        ws = show $ inputWidth v

compileNetInstr h instr = hPutStrLn h $ stringOfNetInstr instr
vstr (NetBits w (ConstMask v)) = show v++":"++show w
vstr (NetBits w (VarId id)) = idName id
stringOfNetInstr (AssignResult v opcode) = vstr v++" "++stringOfOpcode opcode
stringOfNetInstr (OutputBits v) = ".output "++vstr v
stringOfOpcode (BinOp bop u v) = opline (bopStr bop) [u,v]
stringOfOpcode (UnOp uop v) = opline (uopStr uop) [v]
stringOfOpcode (ConcatOp l) = opline "concat" l
stringOfOpcode (SelectOp st en v)
  | st == 0   = unwords ["trunc",show en,vstr v]
  | otherwise = unwords ["select",show st,show en,vstr v]
stringOfOpcode (ExtendOp ext w v) = unwords [exts,vstr v,show w]
  where exts = case ext of ZeroExtend -> "zextend"; SignExtend -> "sextend"

opline op l = unwords $ op:map vstr l
bopStr x = case x of  BitAnd -> "and"
                      BitOr -> "or"
                      BitXor -> "xor"
                      BitEq -> "equ"
                      BitGt -> "gtu"
                      BitAdd -> "add"
                      BitSub -> "sub"

uopStr x = case x of  BitNot -> "not"
                      BitNeg -> "negate"
                      BitAny -> "or"
                      BitParityOdd -> "xor"

destPath = "gcilouts/"

writeCaseFiles caseName f =
  withSuff ".cir" $ \cktf -> 
    withSuff "-server.in" $ \serin ->
      withSuff "-client.in" $ \clin -> f cktf serin clin
  where
  withSuff suff = withFile (destPath++caseName++suff) WriteMode


-- Should be removed after I update my base libraries/ghc
-- |Strict version of 'modifyIORef'
modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
    x <- readIORef ref
    let x' = f x
    x' `seq` writeIORef ref x'
