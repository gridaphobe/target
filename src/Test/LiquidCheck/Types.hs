{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Test.LiquidCheck.Types where

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types

import           GHC


type Constraint = [Pred]
type Variable   = ( String -- the name
                  , Sort   -- the `Sort'
                  )
type Value      = String

instance Symbolic Variable where
  symbol (x, _) = symbol x

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd

type DataConEnv = [(String, SpecType)]
type MeasureEnv = [Measure SpecType DataCon]

boolsort, choicesort :: Sort
boolsort   = FObj $ stringSymbol "Bool"
choicesort = FObj $ stringSymbol "CHOICE"

data Result = Passed !Int
            | Failed !String
            deriving (Show)
