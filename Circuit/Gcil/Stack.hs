module Circuit.Gcil.Stack where

-- TODO change compiler first
-- Change and, or etc. to bitAnd, bitOr etc.
-- Change gblInt and split it to gblBitvec and gblInt

data Stack a = Stack  { buffer   :: [GblMaybe a]
                      , buffhead :: GblInt
                      , rest     :: Maybe (Stack (a,a))
                      , noadjust :: Bool
                      }

buffsize = 5
ptrwidth = 3

empty = Stack { buffer = replicateM buffsize $ gblMaybe Nothing
              , buffhead = constArg ptrwidth 2
              , rest = Nothing
              , noadjust = True
              }

singleton x = condPush True x empty

top stk = muxListOffset 1 (buffhead stk) (buffer stk)

condOp :: Garbled v => GblBit -> v -> GblBit -> Stack v -> GcilMonad (Stack v)
condOp pushCond pushVal popCond stk = do
  -- TODO get a more efficient decoder for 5 possibilities at different lo
  popDone  <- not pushCond >>= and popCond
  pushDone <- xor zapCond pushCond >>= xor popCond -- push AND NOT pop
  popper   <- decoderWithEnable popDone  $ buffhead stk
  pusher   <- decoderWithEnable pushDone $ buffhead stk
  newbuff  <- forM (zip (buffer stk) (drop 1 zapper)) $ \(elt,zap) ->
                condNothing zap elt
  newbuff  <- forM (zip newbuff pusher) $ \(elt,pc) ->
                mux pc elt $ gblMaybe (Just pc)
  bhTouch  <- xor pushDone popDone
  newbh    <- addS (buffhead stk) bhTouch
  -- if popCond and not pushCond, deltaBh == -1
  -- else if pushCond and not popCond, deltaBh == +1
  -- else deltaBh = 0
  deltaBh  <- concat [bitToInt popDone, bitToInt bhTouch]
  result   <- return $ stk { buffer = newbuff, buffhead = newbh }
  if noadjust stk then return $ result { noadjust = False} else adjust result
