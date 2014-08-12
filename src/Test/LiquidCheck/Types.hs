{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Test.LiquidCheck.Types where

import qualified Control.Exception             as Ex
import           Data.Typeable

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types

import           GHC

import qualified Data.Text                     as T

data LiquidException = SmtFailedToProduceOutput
                     | ExpectedValues Response
                     | PreconditionCheckFailed String
  deriving Typeable

instance Show LiquidException where
  show SmtFailedToProduceOutput = "The SMT solver was unable to produce an output value."
  show (ExpectedValues r) = "Expected a Values response from the solver, got: " ++ show r
  show (PreconditionCheckFailed e) = "The pre-condition check for a generated function failed: " ++ e

instance Ex.Exception LiquidException

ensureValues x = do
  a <- x
  case a of
    Values _ -> return a
    r        -> Ex.throw $ ExpectedValues r

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
            deriving (Show)

resultPassed (Passed i) = i
