{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
module Test.LiquidCheck
  ( liquidCheck, testModule, testFun, testOne
  , Constrain(..), Result(..), Testable(..), Test(..), CanTest)
  where

import Control.Applicative
import Control.Arrow                        (first)
import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.Monoid
import Text.Printf                          (printf)

import Language.Fixpoint.Names
import Language.Fixpoint.Types              (Located (..), symbol)
import Language.Haskell.Liquid.CmdLine      (mkOpts)
import Language.Haskell.Liquid.GhcInterface (getGhcInfo)
import Language.Haskell.Liquid.Tidy         (tidySymbol)
import Language.Haskell.Liquid.Types        (GhcInfo (..),
                                             GhcSpec (..), showpp)

import Test.LiquidCheck.Constrain
import Test.LiquidCheck.Constrain.Function  ()
import Test.LiquidCheck.Gen
import Test.LiquidCheck.Testable
import Test.LiquidCheck.Types
import Test.LiquidCheck.Util


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

data Test = forall t. CanTest t => T t
