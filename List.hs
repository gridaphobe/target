module Main where

import Language.Fixpoint.Parse
import Language.Haskell.Liquid.Types (BareType)
import LiquidSMT

mytake :: Int -> [Int] -> [Int]
mytake 0 xs     = xs
mytake _ []     = []
mytake n (x:xs) = x : mytake (n-1) xs

mytake_spec :: BareType
mytake_spec = rr "n:{Int | n >= 0} -> {v:[{v:Int | v >= 0}]<{\\x y -> true}> | n < (len v)} -> {v:[{v:Int | v >= 0}]<{\\x y -> true}> | (len v) = n}"

mytake_spec' :: BareType
mytake_spec' = rr "n:{Int | n >= 0} -> [{v:Int | v >= 0}]<{\\x y -> true}> -> {v:[{v:Int | v >= 0}]<{\\x y -> true}> | (len v) = n}"

main = runGen env $ test mytake 10 mytake_spec'
