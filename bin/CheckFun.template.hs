{-# LANGUAGE LambdaCase #-}
module Main where

import qualified $module$

import Control.Applicative
import Control.Monad
import Data.Time.Clock.POSIX
import System.IO
import System.Timeout
import Text.Printf

import Language.Haskell.Liquid.Types (GhcSpec)
import Test.LiquidCheck
import Test.LiquidCheck.Gen
import Test.LiquidCheck.Util

main :: IO ()
main = do
  spec <- getSpec "$file$"
  putStr ("$fun$" ++ ": ")
  rs <- checkMany spec
  putStrLn "done"
  forM_ rs $ \(d,t,r) -> printf "%d\t%.2f\t%s\n" d t (show r)
  putStrLn ""

checkMany :: GhcSpec -> IO [(Int, Double, Outcome)]
checkMany spec = go 2
  where
    go n      = checkAt n >>= \case
                  (d,Nothing) -> return [(n,d,TimedOut)]
                  (d,Just r)  -> ((n,d,Completed r):) <$> go (n+1)
    checkAt n = do putStrNow (printf "%d " n)
                   timed $ timeout tenMinutes $ runGen spec $ testFun $fun$ "$fun$" n

tenMinutes = 10 * 60 * 1000000

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

putStrNow s = putStr s >> hFlush stdout

data Outcome = Completed Result
             | TimedOut
             deriving (Show)
