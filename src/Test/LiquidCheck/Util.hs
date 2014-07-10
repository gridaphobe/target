{-# LANGUAGE BangPatterns #-}
module Test.LiquidCheck.Util where

import           Control.Exception
import           Control.Monad.IO.Class
import           Debug.Trace
import           GHC.IO.Handle
import           System.IO


io ::  MonadIO m => IO a -> m a
io = liftIO

myTrace :: Show a => String -> a -> a
myTrace s x = trace (s ++ ": " ++ show x) x

safeFromJust :: String -> Maybe a -> a
safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust _   (Just x) = x

silently :: IO a -> IO a
silently act = act
silently !act = do
    hFlush stdout
    hFlush stderr
    bracket setup reset $ \(act, o, e, n) -> act >>= \x -> return $! x
  where
    setup
      = do o <- hDuplicate stdout
           e <- hDuplicate stderr
           n <- openFile "/dev/null" WriteMode
           hDuplicateTo n stdout
           hDuplicateTo n stderr
           return (act,o,e,n)
    reset (_,o,e,n)
      = do hDuplicateTo o stdout
           hDuplicateTo e stderr
           hClose o
           hClose e
           hClose n

