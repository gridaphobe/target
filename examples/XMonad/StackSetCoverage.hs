{-# LANGUAGE LambdaCase #-}
module Main where

import qualified XMonad.StackSet

import Control.Applicative
import           Control.Concurrent.Async
import           Control.Concurrent.MSem
import Control.Monad
import Control.Concurrent.Timeout
import Data.Time.Clock.POSIX
import Data.Timeout
import System.Environment
import System.IO
import Text.Printf

import Language.Haskell.Liquid.Types (GhcSpec)
import Test.LiquidCheck
import Test.LiquidCheck.Gen
import Test.LiquidCheck.Util

main :: IO ()
main = do
  [t]  <- getArgs
  spec <- getSpec "bench/XMonad/StackSet.hs"
  withFile ("_results/XMonad.StackSet"++t++".tsv") WriteMode $ \h -> do
    hPutStrLn h "Function\tDepth\tTime(s)\tResult"
    mapPool 4 (checkMany spec h (read t # Minute)) funs
  putStrLn "done"
  putStrLn ""

mapPool max f xs = do
  sem <- new max
  mapConcurrently (with sem . f) xs

-- checkMany :: GhcSpec -> Handle -> IO [(Int, Double, Outcome)]
checkMany spec h time (T f,sp) = putStrNow (printf "Testing %s..\n" sp) >> go 2
  where
    go 21     = return []
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
    checkAt n = timed $ timeout time $ runGen spec "bench/XMonad/StackSet.hs" $ testFunIgnoringFailure f sp n

--time = 5 # Minute

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

funs = [(T ((XMonad.StackSet.view) :: ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.view")
       ,(T ((XMonad.StackSet.tagMember) :: ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.Bool), "XMonad.StackSet.tagMember")
       ,(T ((XMonad.StackSet.swapMaster) :: XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.swapMaster")
       ,(T ((XMonad.StackSet.peek) :: XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.Maybe XMonad.StackSet.Char), "XMonad.StackSet.peek")
       ,(T ((XMonad.StackSet.new) :: ()-> [()]-> [()]-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char Int ()), "XMonad.StackSet.new")
       ,(T ((XMonad.StackSet.modify') :: (XMonad.StackSet.Stack XMonad.StackSet.Char -> XMonad.StackSet.Stack XMonad.StackSet.Char)-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.modify'")
       ,(T ((XMonad.StackSet.modify) :: XMonad.StackSet.Maybe (XMonad.StackSet.Stack XMonad.StackSet.Char)-> (XMonad.StackSet.Stack XMonad.StackSet.Char    -> XMonad.StackSet.Maybe         (XMonad.StackSet.Stack XMonad.StackSet.Char))-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.modify")
       ,(T ((XMonad.StackSet.member) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.Bool), "XMonad.StackSet.member")
       ,(T ((XMonad.StackSet.mapWorkspace) :: (XMonad.StackSet.Workspace () () XMonad.StackSet.Char -> XMonad.StackSet.Workspace () () XMonad.StackSet.Char)-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.mapWorkspace")
       ,(T ((XMonad.StackSet.mapLayout) :: (() -> ())-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet     () () XMonad.StackSet.Char () ()), "XMonad.StackSet.mapLayout")
       ,(T ((XMonad.StackSet.integrate') :: XMonad.StackSet.Maybe (XMonad.StackSet.Stack XMonad.StackSet.Char)-> [XMonad.StackSet.Char]), "XMonad.StackSet.integrate'")
       ,(T ((XMonad.StackSet.integrate) :: XMonad.StackSet.Stack XMonad.StackSet.Char-> [XMonad.StackSet.Char]), "XMonad.StackSet.integrate")
       ,(T ((XMonad.StackSet.insertUp) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.insertUp")
       ,(T ((XMonad.StackSet.greedyView) :: ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.greedyView")
       ,(T ((XMonad.StackSet.focusMaster) :: XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.focusMaster")
       ,(T ((XMonad.StackSet.findTag) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.Maybe ()), "XMonad.StackSet.findTag")
       ,(T ((XMonad.StackSet.filter) :: (XMonad.StackSet.Char -> XMonad.StackSet.Bool)-> XMonad.StackSet.Stack XMonad.StackSet.Char-> XMonad.StackSet.Maybe     (XMonad.StackSet.Stack XMonad.StackSet.Char)), "XMonad.StackSet.filter")
       ,(T ((XMonad.StackSet.ensureTags) :: ()-> [()]-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()-> XMonad.StackSet.StackSet () () XMonad.StackSet.Char () ()), "XMonad.StackSet.ensureTags")
       ,(T ((XMonad.StackSet.differentiate) :: [XMonad.StackSet.Char]-> XMonad.StackSet.Maybe     (XMonad.StackSet.Stack XMonad.StackSet.Char)), "XMonad.StackSet.differentiate")
       ,(T ((XMonad.StackSet.currentTag) :: XMonad.StackSet.StackSet () () XMonad.StackSet.Char () () -> ()), "XMonad.StackSet.currentTag")]
