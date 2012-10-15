-- Used as a debugging aid to convert DIMACS output into a more readable form
-- The idea is that any DIMACS query generated in dimacsouts/ is accompanied
-- by a format specifier. The contents of that file is output to the console
-- verbatim, except for $UInt[ ... ] and other $ tokens. Other unrecognized
-- $tokens are removed.

import Control.Monad
import Data.Char
import Data.List
import qualified Data.Map as M
import Text.ParserCombinators.ReadP
import System.Environment

signOrInt '+' = True
signOrInt '-' = True
signOrInt c = isDigit c

(><) = liftM2 (++)

-- Assuming it is a SAT instance and we have vmap
-- Most significant bit indices come first
formatSat :: (Int -> Bool) -> ReadP String
formatSat vmap = liftM concat $ liftM2 (:) firstLiteral 
                              $ manyTill (literal +++ macro) eof where
  firstLiteral = munch (/='$')
  literal = munch isSpace >< munch1 (\c -> c/='$'&&c/='[') >< munch (/='$')
  macro = do char '$'
             header <- munch1 isAlpha
             inds <- option [] $ between (nows '[') (nows ']') 
                     $ sepBy bitind (munch1 isSpace)
             return $ processMacro vmap (map toLower header) inds
  nows c = skipSpaces >> char c
  bitind :: ReadP Int
  bitind = do s <- munch signOrInt
              let l = length s
                  r = read s
              if l == 0 then pfail
              else if isDigit $ head s then return r
              else if l == 1 then pfail 
              else return r

processMacro :: (Int -> Bool) -> String -> [Int] -> String
processMacro vmap "uint" inds = show $ toUInt vmap inds
processMacro vmap "sint" inds = show $ toSInt vmap inds
processMacro vmap "bool" inds = show $ toBool vmap (head inds)
processMacro _ _ _ = ""

toBool vmap i | i > 0 = vmap i
              | i < 0 = not $ vmap (-i)
              | otherwise = undefined

toUInt vmap inds = foldl' (\v i -> 2*v+imap i) 0 inds
  where imap i = if toBool vmap i then 1 else 0

toSInt vmap inds = offset + toUInt vmap (tail inds) where
  offset = if toBool vmap (head inds) then -(2^(length inds-1)) else 0

formatMain solverOut tmpl | status == "UNSAT" = "UNSAT\n"
                          | status == "SAT"   = "SAT\n"++formatted
                          | otherwise = "Neither SAT nor UNSAT"
  where
  formatted = fst $ head $ readP_to_S (formatSat vmWrap) tmpl
  outWords = words solverOut
  status = head outWords
  vmap = M.fromList [(i,b) | tok <- map read $ tail outWords
                           , let i = abs tok; b = tok>0]
  vmWrap = (vmap M.!)

{- target for now:
for(i=j=0;j<n;++i) {
  // does i ever surpass j
  while(dist(arr[i],arr[j])<dist(arr[i],arr[j+1])) ++j;
  updateWith(dist(arr[i],arr[j]));
}

conjureInputs UInt, SInt, Bool, assert, show,
-}

main = do args <- getArgs
          if length args /= 1 
            then putStrLn "Usage: FormatDimacs <template>"
            else do
              tmpl <- readFile $ head args
              interact (\solverOut -> formatMain solverOut tmpl)

