{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Test.Target.Types where

import qualified Control.Monad.Catch           as Ex
import qualified Data.Text                     as T
import           Data.Typeable

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types

import           GHC


data TargetException
  = SmtFailedToProduceOutput
  | SmtError String
  | ExpectedValues Response
  | PreconditionCheckFailed String
  | EvalError String
  deriving Typeable

instance Show TargetException where
  show SmtFailedToProduceOutput
    = "The SMT solver was unable to produce an output value."
  show (SmtError s)
    = "Unexpected error from the solver: " ++ s
  show (ExpectedValues r)
    = "Expected a Values response from the solver, got: " ++ show r
  show (PreconditionCheckFailed e)
    = "The pre-condition check for a generated function failed: " ++ e
  show (EvalError s)
    = "Couldn't evaluate a concrete refinement: " ++ s

instance Ex.Exception TargetException

ensureValues :: Ex.MonadThrow m => m Response -> m Response
ensureValues x = do
  a <- x
  case a of
    Values _ -> return a
    r        -> Ex.throwM $ ExpectedValues r

type Constraint = [Pred]
type Variable   = ( Symbol -- the name
                  , Sort   -- the `Sort'
                  )
type Value      = T.Text

instance Symbolic Variable where
  symbol (x, _) = symbol x

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd

type DataConEnv = [(Symbol, SpecType)]
type MeasureEnv = [Measure SpecType DataCon]

boolsort, choicesort :: Sort
boolsort   = FObj "Bool"
choicesort = FObj "CHOICE"

data Result = Passed !Int
            | Failed !String
            | Errored !String
            deriving (Show, Typeable)

-- resultPassed (Passed i) = i
