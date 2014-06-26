{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module JSON where

import Data.Aeson
import Data.Maybe
import GHC.Generics

import Test.LiquidCheck
import Test.SmallCheck.Series

-- FIXME: need a more interesting type than Coord, preferably with some constraints, like XMONADD
{-@ data Coord = Coord {x :: Int, y :: Int} @-}
data Coord = Coord { x :: Int, y :: Int } deriving (Show, Generic, Eq)

instance FromJSON Coord
instance ToJSON Coord

instance Constrain Coord
instance Monad m => Serial m Coord

-- FIXME: this measure makes sure that True and False are in the environment...
{-@ measure prop :: Bool -> Prop
    prop (True)  = true
    prop (False) = false
 @-}
{-@ type True = {v:Bool | (prop v)} @-}
{-@ prop_json_inv :: Coord -> True @-}
prop_json_inv :: Coord -> Bool
prop_json_inv c = fromJust (decode (encode c)) == c
