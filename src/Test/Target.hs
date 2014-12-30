{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
module Test.Target
  ( liquidCheck, testModule, testFun, testFunIgnoringFailure, testOne, testOneMaxSC, testOneMax
  , Targetable(..), Result(..), Testable(..), Test(..), CanTest)
  where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Text.Printf                          (printf)

import           Language.Fixpoint.Names
import           Language.Haskell.Liquid.Tidy         (tidySymbol)

import           Test.Target.Targetable
import           Test.Target.Targetable.Function  ()
import           Test.Target.Monad
import           Test.Target.Testable
import           Test.Target.Types
import           Test.Target.Util


testModule :: FilePath -> [Gen Result] -> IO ()
testModule m ts
  = do sp <- getSpec m
       forM_ ts $ \t -> do
         res <- runGen sp m t
         case res of
           Passed n -> printf "OK. Passed %d tests\n\n" n
           Failed x -> printf "Found counter-example: %s\n\n" x

liquidCheck :: CanTest f => f -> String -> Int -> Gen Result
liquidCheck f name d
  = do io $ printf "Testing %s\n" name -- (showpp ty)
       testFun f name d

testFun :: CanTest f => f -> String -> Int -> Gen Result
testFun f name d
  = do ty <- safeFromJust "testFun" . lookup (symbol name) <$> gets sigs
       modify $ \s -> s { depth = d }
       test f d ty

tidyVar :: Symbolic a => a -> Symbol
tidyVar = tidySymbol . symbol

testOne :: CanTest f => f -> String -> Int -> FilePath -> IO Result
testOne f name d path
  = do sp <- getSpec path
       runGen sp path $ testFun f name d

testOneMax :: CanTest f => f -> String -> Int -> Int -> FilePath -> IO Result
testOneMax f name d max path
  = do sp <- getSpec path
       runGen sp path $ setMaxSuccess max >> testFun f name d

testOneMaxSC :: CanTest f => f -> String -> Int -> Int -> FilePath -> IO Result
testOneMaxSC f name d max path
  = do sp <- getSpec path
       runGen sp path $ setMaxSuccess max >> modify (\s -> s {scDepth = True}) >> testFun f name d

testFunIgnoringFailure :: CanTest f => f -> String -> Int -> Gen Result
testFunIgnoringFailure f name d
  = do modify $ \s -> s { keepGoing = True }
       testFun f name d

data Test = forall t. CanTest t => T t
