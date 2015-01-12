{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import qualified XMonad.StackSet

import           Control.Applicative
import           Control.Concurrent.Async
import           Control.Concurrent.MSem
import           Control.Concurrent.Timeout
import           Control.Monad.Catch
import           Control.Monad
import           Data.Time.Clock.POSIX
import           Data.Timeout
import           System.Environment
import           System.IO
import           Text.Printf

import           Language.Haskell.Liquid.Types (GhcSpec)
import           Test.Target
import           Test.Target.Monad

instance Show (a -> b) where
  show _ = "<function>"

main :: IO ()
main = do
  [t]  <- getArgs
  withFile ("_results/XMonad.StackSet-" ++ t ++ ".tsv") WriteMode $ \h -> do
    hPutStrLn h "Function\tDepth\tTime(s)\tResult"
    mapPool 8 (checkMany h (read t # Minute)) funs
  putStrLn "done"
  putStrLn ""

mapPool max f xs = do
  sem <- new max
  mapConcurrently (with sem . f) xs


-- checkMany :: GhcSpec -> Handle -> IO [(Int, Double, Outcome)]
checkMany h time (f,sp) = putStrNow (printf "Testing %s..\n" sp) >> go 2
  where
    go 21     = return []
    go n      = checkAt f sp n time >>= \case
                  (d,Nothing) -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    return [(n,d,TimeOut)]
                  --NOTE: timeout is a bit unreliable..
                  (d,_) | round d >= time #> Second -> do
                    let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                    putStrLn s >> hFlush stdout
                    hPutStrLn h s >> hFlush h
                    putStrLn "WARNING: timeout seems to have been ignored..."
                    return [(n,d,TimeOut)]
                  --NOTE: sometimes the timeout causes an error instead of a timeout exn
                  (d,Just (Errored s)) -> return [(n,d,Complete (Errored s))]
                  --NOTE: ignore counter-examples for the sake of exploring coverage
                  --(d,Just (Failed s)) -> return [(n,d,Complete (Failed s))]
                  (d,Just r)  -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show (Complete r))
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    ((n,d,Complete r):) <$> go (n+1)

checkAt :: Test -> String -> Int -> Timeout -> IO (Double, Maybe Result)
checkAt (T f) sp n time = timed $ do
  r <- try $ timeout time $ targetResultWithStr f sp "bench/XMonad/StackSet.hs" (defaultOpts {depth=n, keepGoing=True})
  case r of
    Left (e :: SomeException) -> return $ Just $ Errored $ show e
    Right r                   -> return r

-- time = 5 # Minute

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

funs = [(T ((XMonad.StackSet.new) :: XMonad.StackSet.Int-> [XMonad.StackSet.Int]-> [XMonad.StackSet.Int]-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.new")
       ,(T ((XMonad.StackSet.view) :: XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.view")
       ,(T ((XMonad.StackSet.greedyView) :: XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.greedyView")
       ,(T ((XMonad.StackSet.lookupWorkspace) :: XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.Maybe XMonad.StackSet.Int), "XMonad.StackSet.lookupWorkspace")
       ,(T ((XMonad.StackSet.modify) :: XMonad.StackSet.Maybe (XMonad.StackSet.Stack XMonad.StackSet.Char)-> (XMonad.StackSet.Stack XMonad.StackSet.Char    -> XMonad.StackSet.Maybe         (XMonad.StackSet.Stack XMonad.StackSet.Char))-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.modify")
       ,(T ((XMonad.StackSet.modify') :: (XMonad.StackSet.Stack XMonad.StackSet.Char -> XMonad.StackSet.Stack XMonad.StackSet.Char)-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.modify'")
       ,(T ((XMonad.StackSet.peek) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> XMonad.StackSet.Maybe XMonad.StackSet.Char), "XMonad.StackSet.peek")
       ,(T ((XMonad.StackSet.integrate) :: XMonad.StackSet.Stack XMonad.StackSet.Char-> [XMonad.StackSet.Char]), "XMonad.StackSet.integrate")
       ,(T ((XMonad.StackSet.integrate') :: XMonad.StackSet.Maybe (XMonad.StackSet.Stack XMonad.StackSet.Char)-> [XMonad.StackSet.Char]), "XMonad.StackSet.integrate'")
       ,(T ((XMonad.StackSet.differentiate) :: [XMonad.StackSet.Char]-> XMonad.StackSet.Maybe     (XMonad.StackSet.Stack XMonad.StackSet.Char)), "XMonad.StackSet.differentiate")
       ,(T ((XMonad.StackSet.filter) :: (XMonad.StackSet.Char -> XMonad.StackSet.Bool)-> XMonad.StackSet.Stack XMonad.StackSet.Char-> XMonad.StackSet.Maybe     (XMonad.StackSet.Stack XMonad.StackSet.Char)), "XMonad.StackSet.filter")
       ,(T ((XMonad.StackSet.index) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> [XMonad.StackSet.Char]), "XMonad.StackSet.index")
       ,(T ((XMonad.StackSet.focusUp) :: XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.focusUp")
       ,(T ((XMonad.StackSet.focusDown) :: XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.focusDown")
       ,(T ((XMonad.StackSet.swapUp) :: XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.swapUp")
       ,(T ((XMonad.StackSet.swapDown) :: XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.swapDown")
       --FIXME: why does this one loop forever and ignore the timeout??
       --,(T ((XMonad.StackSet.focusWindow) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.focusWindow")
       ,(T ((XMonad.StackSet.screens) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> [XMonad.StackSet.Screen      XMonad.StackSet.Int      XMonad.StackSet.Int      XMonad.StackSet.Char      XMonad.StackSet.Int      XMonad.StackSet.Int]), "XMonad.StackSet.screens")
       ,(T ((XMonad.StackSet.workspaces) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> [XMonad.StackSet.Workspace      XMonad.StackSet.Int XMonad.StackSet.Int XMonad.StackSet.Char]), "XMonad.StackSet.workspaces")
       ,(T ((XMonad.StackSet.allWindows) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> [XMonad.StackSet.Char]), "XMonad.StackSet.allWindows")
       ,(T ((XMonad.StackSet.currentTag) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> XMonad.StackSet.Int), "XMonad.StackSet.currentTag")
       ,(T ((XMonad.StackSet.tagMember) :: XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.Bool), "XMonad.StackSet.tagMember")
       ,(T ((XMonad.StackSet.renameTag) :: XMonad.StackSet.Int-> XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.renameTag")
       ,(T ((XMonad.StackSet.ensureTags) :: XMonad.StackSet.Int-> [XMonad.StackSet.Int]-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.ensureTags")
       ,(T ((XMonad.StackSet.mapWorkspace) :: (XMonad.StackSet.Workspace   XMonad.StackSet.Int XMonad.StackSet.Int XMonad.StackSet.Char -> XMonad.StackSet.Workspace      XMonad.StackSet.Int XMonad.StackSet.Int XMonad.StackSet.Char)-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.mapWorkspace")
       ,(T ((XMonad.StackSet.mapLayout) :: (XMonad.StackSet.Int -> XMonad.StackSet.Int)-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.mapLayout")
       ,(T ((XMonad.StackSet.member) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.Bool), "XMonad.StackSet.member")
       ,(T ((XMonad.StackSet.findTag) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.Maybe XMonad.StackSet.Int), "XMonad.StackSet.findTag")
       ,(T ((XMonad.StackSet.insertUp) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.insertUp")
       ,(T ((XMonad.StackSet.delete) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.delete")
       ,(T ((XMonad.StackSet.float) :: XMonad.StackSet.Char-> XMonad.StackSet.RationalRect-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.float")
       ,(T ((XMonad.StackSet.sink) :: XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.sink")
       ,(T ((XMonad.StackSet.swapMaster) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.swapMaster")
       ,(T ((XMonad.StackSet.shiftMaster) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.shiftMaster")
       ,(T ((XMonad.StackSet.focusMaster) :: XMonad.StackSet.StackSet  XMonad.StackSet.Int  XMonad.StackSet.Int  XMonad.StackSet.Char  XMonad.StackSet.Int  XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.focusMaster")
       ,(T ((XMonad.StackSet.shift) :: XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.shift")
       ,(T ((XMonad.StackSet.shiftWin) :: XMonad.StackSet.Int-> XMonad.StackSet.Char-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int-> XMonad.StackSet.StackSet     XMonad.StackSet.Int     XMonad.StackSet.Int     XMonad.StackSet.Char     XMonad.StackSet.Int     XMonad.StackSet.Int), "XMonad.StackSet.shiftWin")]
