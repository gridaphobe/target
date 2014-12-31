{-# LANGUAGE ExistentialQuantification #-}
module Test.Target
  ( target, targetResult, targetWith, targetResultWith
  , Result(..), Testable
  , TargetOpts(..), defaultOpts
  , Test(..)
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.State
-- import qualified Language.Haskell.TH             as TH
import           System.Process                  (terminateProcess)
import           Text.Printf                     (printf)

import           Language.Fixpoint.Names
import           Language.Fixpoint.SmtLib2       hiding (verbose)

import           Test.Target.Monad
import           Test.Target.Targetable ()
import           Test.Target.Targetable.Function ()
import           Test.Target.Testable
import           Test.Target.Types
import           Test.Target.Util


target :: Testable f => f -> String -> FilePath -> IO ()
target f name path
  = targetWith f name path defaultOpts

targetResult :: Testable f => f -> String -> FilePath -> IO Result
targetResult f name path
  = targetResultWith f name path defaultOpts

targetWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO ()
targetWith f name path opts
  = do res <- targetResultWith f name path opts
       case res of
         Passed n -> printf "OK. Passed %d tests\n\n" n
         Failed x -> printf "Found counter-example: %s\n\n" x

targetResultWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO Result
targetResultWith f name path opts
  = do when (verbose opts) $
         printf "Testing %s\n" name
       sp  <- getSpec path
       ctx <- mkContext (solver opts)
       runTarget opts (initState path sp ctx) (do
         ty <- safeFromJust "targetResultWith" . lookup (symbol name) <$> gets sigs
         test f (depth opts) ty)
        `finally` killContext ctx
  where
    mkContext = if logging opts then makeContext else makeContextNoLog
    killContext ctx = terminateProcess (pId ctx) >> cleanupContext ctx

data Test = forall t. Testable t => T t
