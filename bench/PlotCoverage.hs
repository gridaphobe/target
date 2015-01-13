{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ViewPatterns      #-}
module Main where

import Control.Monad
import qualified Data.ByteString.Lazy as LB
import qualified Data.Csv as C
import qualified Data.Vector as V
import Data.Maybe
import Data.String
import qualified Data.Text as T
-- import Graphics.Rendering.Chart.Easy hiding (element, (<.>))
-- import Graphics.Rendering.Chart.Backend.Diagrams
import Prelude hiding (readFile)
import Text.Printf
import Text.XML
import Text.XML.Cursor
import System.Environment
import System.FilePath
import System.IO hiding (readFile)
import System.Process

main = do
  [fn] <- getArgs
  sts  <- getStats fn
  withFile (printf "bench/%s.csv" fn) WriteMode $ \h ->
    LB.hPutStr h $ C.encodeByName hpcHeader $ map C.toNamedRecord sts

  

-- depths :: [Int]
-- depths = [2..20]

getStats :: String -> IO [HpcStats]
getStats m = forM ["1", "5", "10", "15", "20", "25", "30"] $ \d -> do
               system $ printf "hpc report --xml-output --hpcdir=_results _results/%s-%s.tix > %s-%s.xml" m d m d
               readHpc $ fromString $ printf "%s-%s.xml" m (d::String)

-- mkPlot name stats = toFile (def {_fo_format = EPS}) (name<.>"eps") $ do
--     layout_title .= name
--     layout_title_style . font_size .= 36
--     layout_legend .= Just (legend_label_style . font_size .~ 24 $ def)
--     layout_x_axis . laxis_style . axis_label_style . font_size .= 24
--     layout_y_axis . laxis_style . axis_label_style . font_size .= 24
--     layout_y_axis . laxis_override .= axisGridHide
--     plotLine "expressions" exprs stats
--     plotLine "booleans" booleans stats
--     plotLine "always True" alwaysTrue stats
--     plotLine "always False" alwaysFalse stats
--     plotLine "alternatives" alts stats
--     plotLine "local functions" local stats
    
--     -- V.forM_ stats $ \s -> plot (line (tool r) [ zip depths (map LogValue $ times r) ] )

-- plotLine name f stats = when noNaN $ plot $ line name [ points ]
--   where
--     noNaN  = not $ any (isNaN . snd) points
--     points = [ (depth s, p) | s <- stats, let p = fst (f s) / snd (f s)]

data HpcStats = HpcStats 
  { name         :: T.Text
  , depth        :: Int
  , exprs        :: (Double,Double) 
  , booleans     :: (Double,Double)
  , alwaysTrue   :: (Double,Double)
  , alwaysFalse  :: (Double,Double)
  -- , guards       :: (Double,Double)
  -- , conditionals :: (Double,Double)
  , alts         :: (Double,Double)
  , local        :: (Double,Double)
  }

instance C.ToNamedRecord HpcStats where
  toNamedRecord (HpcStats {..}) =
    C.namedRecord [ "depth"           C..= depth
                  , "expressions"     C..= exprs
                  , "booleans"        C..= booleans
                  , "always-true"     C..= alwaysTrue
                  , "always-false"    C..= alwaysFalse
                  , "alternatives"    C..= alts
                  , "local-functions" C..= local
                  ]

instance C.ToField (Double,Double) where
  toField (x,y) = C.toField (x / y)

hpcHeader :: C.Header
hpcHeader = V.fromList [ "depth", "expressions", "booleans"
                       , "always-true", "always-false"
                       , "alternatives", "local-functions"
                       ]

readHpc = fmap toHpcStats . readFile def

toHpcStats :: Document -> HpcStats
toHpcStats (fromDocument -> cur) 
  = HpcStats { name = fromJust $ T.stripSuffix "Coverage" name 
             , depth = read $ T.unpack depth, .. }
  where
    file = T.pack . takeBaseName . dropExtension . T.unpack . T.concat 
         $ cur $| attribute "name"
    [name, depth] = T.splitOn "-" file
    summary = head $ cur $/ element "summary"
    exprs = head $ summary $/ element "exprs" &| mkCount
    booleans = head $ summary $/ element "booleans" &| mkCount
    alwaysTrue = head $ summary $/ element "booleans" &| mkTrue
    alwaysFalse = head $ summary $/ element "booleans" &| mkFalse
    alts = head $ summary $/ element "alts" &| mkCount
    local = head $ summary $/ element "local" &| mkCount

mkCount :: Cursor -> (Double,Double)
mkCount c = ( head (c $| attribute "count" &| tread) 
            , head (c $| attribute "boxes" &| tread)
            )
mkTrue :: Cursor -> (Double,Double)
mkTrue c = ( head (c $| attribute "true" &| tread) 
           , head (c $| attribute "boxes" &| tread)
           )
mkFalse :: Cursor -> (Double,Double)
mkFalse c = ( head (c $| attribute "false" &| tread) 
            , head (c $| attribute "boxes" &| tread)
            )

tread = read . T.unpack
