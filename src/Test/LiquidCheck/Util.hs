module Test.LiquidCheck.Util where

import           Control.Monad.IO.Class
import           Debug.Trace


io ::  MonadIO m => IO a -> m a
io = liftIO

myTrace :: Show a => String -> a -> a
myTrace s x = trace (s ++ ": " ++ show x) x

safeFromJust :: String -> Maybe a -> a
safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust _   (Just x) = x
