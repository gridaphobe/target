module Main where

-- import Language.Fixpoint.Parse
-- import Language.Haskell.Liquid.Types (BareType)
-- import LiquidSMT

{-@ mytake :: n:Nat -> xs:[a] -> {v:[a] | (Min (len v) n (len xs))} @-}
mytake :: Int -> [a] -> [a]
mytake 0 xs     = []
mytake _ []     = []
mytake n (x:xs) = x : mytake (n-1) xs

-- mytake_spec :: BareType
-- mytake_spec = rr $ unlines [ "n:{Int | n >= 0} -> "
--                            , "[{v:Int | v >= 0}]<{\\x y -> true}> -> "
--                            , "{v:[{v:Int | v >= 0}]<{\\x y -> true}> | (len v) = n}"]

-- main = runGen env $ test mytake 5 mytake_spec

-- main = testOne mytake 'mytake "List.hs"
main = undefined
