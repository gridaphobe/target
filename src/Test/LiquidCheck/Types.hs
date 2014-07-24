{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Test.LiquidCheck.Types where

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types

import           GHC

import qualified Data.Text.Lazy as T

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
