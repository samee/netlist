-- Using the same pattern as Circuit.NetList.Gcil, I want this:
-- dimacsList $ do v <- newInt width
--                 v2 <- newInt width2
--                 outputs <- liftNet $ awesomeCircuit v v2
--                 assert =<< f output -- assertEq is good enough for cycles
--                 dimacsShow $ "hello world: "++show outputs
--
-- dimacsShow works with FormatDimacs
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict

data DimacsInstr = CalcInstr NetInstr
                 | FreshBits NetBits
                 | AssertTrue NetBits -- assert non-zero
                 | ShowString String
                 | ShowBits BitFormat NetBits

data BitFormat = UIntFormat | SIntFormat | BoolFormat

type DmMonad = WriterT [DimacsInstr] (State Int)
dimacsList :: DmMonad a -> [DimacsInstr]
dimacsList ckt = evalState (execWriterT ckt) 1

liftNet :: NetWriter a -> DmMonad a
liftNet m = do ((a,l),endId) <- gets $ netList $ addend
               tell $ map CalcInstr l
               put endId
               return a
  where addend = do r <- m
                    end <- nextBitId
                    return (r,end)

freshBits w = do id <- state $ \id -> (id,id+1)
                 let z = conjureBits w id
                 tell $ FreshBits z
                 return z
freshInt = liftM intFromBits . freshBits
freshBool = freshBits 1 >>= liftNet . lsb

dmAssert b = do z <- bitify b; tell [AssertTrue z]

-- Mechanisms for dmShow to work correctly
data FormatToken = UIntTok NetUInt | SIntTok NetSInt | BoolTok NetBool
                 | StringTok String

class DmShow a where dmShow :: a -> [FormatToken]
instance DmShow [FormatToken] where dmShow = id
instance DmShow String  where dmShow = (:[]).StringTok
instance DmShow NetUInt where dmShow = (:[]).UIntTok
instance DmShow NetSInt where dmShow = (:[]).SIntTok
instance DmShow NetBool where dmShow = (:[]).BoolTok

a -|- b = dmShow a ++ dmShow b

-- Okay, so it accepts more than just strings, so what?
dmPutStrLn a = mapM compileTok (a-|-"\n")

compileTok :: FormatToken -> DimacsInstr
compileTok (StringTok s) = tell $ ShowString s
compileTok (ShowBits UIntTok x) = tell . ShowBits UIntFormat =<< bitify x
compileTok (ShowBits SIntTok x) = tell . ShowBits SIntFormat =<< bitify x
compileTok (ShowBits BoolTok x) = tell . ShowBits BoolFormat =<< bitify x

-- TODO mechanisms for burnSatQuery ... should include a StateT IO monad
-- with a hashtable and other things
burnSatQuery caseName bytecode = writeCaseFiles caseName $ \qfile tmplfile -> do
  burnState <- newBurnState qfile tmplfile
  runState burnCore burnState
  where 
    burnCore = forM_ bytecode $ \bc -> case bc of
      AssertTrue x -> putClause =<< bitList x
      ShowString s -> putTmpl s
      ShowBits fmt x -> showBits fmt =<< bitList x
      FreshBits x -> indexNewBits x
      CalcInstr (OutputBits x) -> showBits UIntTok x
      -- TODO special handling of concat, select and extend
      CalcInstr (AssignResult x op) -> do indexNewBits x
                                          -- TODO

    showBits fmt xz = putTmpl $ tmplFmt fmt ++ "["
                                ++ unwords (map show xz) ++ "]"

tmplFmt UIntTok = "$uint"
tmplFmt SIntTok = "$sint"
tmplFmt BoolTok = "$bool"


writeCaseFiles caseName f = withSuff ".dimacs" $ \qf -> withSuff ".tmpl" (f qf)
  where withSuff s = withFile ("dimacsOut/"++caseName++s)
