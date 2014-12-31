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

-- | Test whether a function inhabits its refinement type by enumerating valid
-- inputs and calling the function.
target :: Testable f
       => f -- ^ the function
       -> String -- ^ the name of the function
       -> FilePath -- ^ the path to the module that defines the function
       -> IO ()
target f name path
  = targetWith f name path defaultOpts

-- | Like 'target', but returns the 'Result' instead of printing to standard out.
targetResult :: Testable f => f -> String -> FilePath -> IO Result
targetResult f name path
  = targetResultWith f name path defaultOpts

-- | Like 'target', but accepts options to control the enumeration depth,
-- solver, and verbosity.
targetWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO ()
targetWith f name path opts
  = do res <- targetResultWith f name path opts
       case res of
         Passed n -> printf "OK. Passed %d tests\n\n" n
         Failed x -> printf "Found counter-example: %s\n\n" x

-- | Like 'targetWith', but returns the 'Result' instead of printing to standard out.
targetResultWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO Result
targetResultWith f name path opts
  = do when (verbose opts) $
         printf "Testing %s\n" name
       sp  <- getSpec path
       ctx <- mkContext (solver opts)
       runTarget opts (initState path sp ctx) (do
         ty <- safeFromJust "targetResultWith" . lookup (symbol name) <$> gets sigs
         test f ty)
        `finally` killContext ctx
  where
    mkContext = if logging opts then makeContext else makeContextNoLog
    killContext ctx = terminateProcess (pId ctx) >> cleanupContext ctx

data Test = forall t. Testable t => T t
