{-# LANGUAGE ExistentialQuantification #-}
module Test.LiquidCheck
  ( liquidCheck, testModule, testFun, testOne
  , Constrain(..), Result(..), Testable(..), Test(..))
  where

import           Control.Applicative
import           Control.Arrow                        (first)
import           Control.Monad
import           Control.Monad.State
import           Data.Maybe
import           Data.Monoid
import           Text.Printf                          (printf)

import           Language.Fixpoint.Types              (Located (..), symbol)
import           Language.Haskell.Liquid.CmdLine      (mkOpts)
import           Language.Haskell.Liquid.GhcInterface (getGhcInfo)
import           Language.Haskell.Liquid.Types        (GhcInfo (..),
                                                       GhcSpec (..), showpp)

import           Test.LiquidCheck.Constrain
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Testable
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


testModule :: FilePath -> [Gen Result] -> IO ()
testModule m ts
  = do sp <- getSpec m
       forM_ ts $ \t -> do
         res <- runGen sp t
         case res of
           Passed n -> printf "OK. Passed %d tests\n\n" n
           Failed x -> printf "Found counter-example: %s\n\n" x

liquidCheck :: Testable f => f -> String -> Int -> Gen Result
liquidCheck = testFun

testFun :: Testable f => f -> String -> Int -> Gen Result
testFun f name d
  = do ty <- safeFromJust "testFun" . lookup (symbol name) <$> gets sigs
       io $ printf "Testing %s\n" name -- (showpp ty)
       modify $ \s -> s { depth = d }
       test f d ty

testOne :: Testable f => Int -> f -> String -> FilePath -> IO Result
testOne d f name path
  = do sp <- getSpec path
       let ty = val $ safeFromJust "testOne" $ lookup name $ map (first showpp) $ tySigs sp
       runGen sp $ test f d ty

-- mkTest :: TH.Name -> TH.ExpQ
-- mkTest f = do loc <- TH.location
--               let name = show f
--                   file = TH.loc_filename loc
--               [| testOne $(TH.varE f) $(TH.stringE name) $(TH.stringE file) |]

data Test = forall t. Testable t => T t
instance Testable Test where
  test (T t) = test t

