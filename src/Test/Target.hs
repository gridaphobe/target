{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
module Test.Target
  ( target, targetResult, targetWith, targetResultWith
  , Targetable(..)
  , TargetOpts(..), defaultOpts
  , Result(..), Testable(..)
  , Test(..), CanTest
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
-- import qualified Language.Haskell.TH             as TH
import           Text.Printf                     (printf)

import           Language.Fixpoint.Names

import           Test.Target.Monad
import           Test.Target.Targetable
import           Test.Target.Targetable.Function ()
import           Test.Target.Testable
import           Test.Target.Types
import           Test.Target.Util


target :: CanTest f => f -> String -> FilePath -> IO ()
target f name path
  = targetWith f name path defaultOpts

targetResult :: CanTest f => f -> String -> FilePath -> IO Result
targetResult f name path
  = targetResultWith f name path defaultOpts

targetWith :: CanTest f => f -> String -> FilePath -> TargetOpts -> IO ()
targetWith f name path opts
  = do res <- targetResultWith f name path opts
       case res of
         Passed n -> printf "OK. Passed %d tests\n\n" n
         Failed x -> printf "Found counter-example: %s\n\n" x

targetResultWith :: CanTest f => f -> String -> FilePath -> TargetOpts -> IO Result
targetResultWith f name path opts
  = do when (verbose opts) $
         printf "Testing %s\n" name
       sp <- getSpec path
       runGen opts sp path $ do
         ty <- safeFromJust "targetResultWith" . lookup (symbol name) <$> gets sigs
         test f (depth opts) ty

data Test = forall t. CanTest t => T t
