{-# LANGUAGE LambdaCase #-}
module Main where

import qualified $module$

import Control.Applicative
import Control.Monad
import Control.Concurrent.Timeout
import Data.Time.Clock.POSIX
import Data.Timeout
import System.IO
import Text.Printf

import Language.Haskell.Liquid.Types (GhcSpec)
import Test.Target
import Test.Target.Monad
import Test.Target.Util

main :: IO ()
main = do
  spec <- getSpec "$file$"
  withFile "_results/$module$.tsv" WriteMode $ \h -> do
    hPutStrLn h "Function\tDepth\tTime(s)\tResult"
    mapM_ (checkMany spec h) funs
  putStrLn "done"
  putStrLn ""

-- checkMany :: GhcSpec -> Handle -> IO [(Int, Double, Outcome)]
checkMany spec h (T f,sp) = putStrNow (printf "Testing %s..\n" sp) >> go 2
  where
    go 11     = return []
    go n      = checkAt n >>= \case
                  (d,Nothing) -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    return [(n,d,TimeOut)]
                  --NOTE: ignore counter-examples for the sake of exploring coverage
                  --(d,Just (Failed s)) -> return [(n,d,Completed (Failed s))]
                  (d,Just r)  -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show (Complete r))
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    ((n,d,Complete r):) <$> go (n+1)
    checkAt n = timed $ timeout time $ runGen spec "$file$" $ testFunIgnoringFailure f sp n

time = $timeout$ # Minute

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

putStrNow s = putStr s >> hFlush stdout

data Outcome = Complete Result
             | TimeOut
             deriving (Show)

funs = [$funs$]
