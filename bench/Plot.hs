module Main where

import Control.Applicative
import qualified Data.ByteString.Lazy as LB
import Data.Csv hiding ((.=))
import qualified Data.Vector as V
import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Diagrams
import System.Environment
import System.FilePath


data TestResult 
  = TestResult { tool :: String
               , times :: [Double] 
               } deriving (Read, Show)

instance FromRecord TestResult where
  parseRecord v = do
    tool  <- v .! 1
    times <- filter (/="X") <$> sequence [ v .! n | n <- [2..20] ]
    return $ TestResult tool $ map read times

main = do
  [fn] <- getArgs
  csv  <- LB.readFile fn
  case decode HasHeader csv of
    Left e   -> error e
    Right rs -> mkPlot (replaceExtension fn ".eps") rs

depths :: [Int]
depths = [2..20]

mkPlot fn rs = toFile (def {_fo_format = EPS}) fn $ do
    layout_title .= (takeFileName $ dropExtension fn)
    layout_title_style . font_size .= 36
    layout_legend .= Just (legend_label_style . font_size .~ 24 $ def)
    layout_x_axis . laxis_style . axis_label_style . font_size .= 24
    layout_y_axis . laxis_style . axis_label_style . font_size .= 24
    layout_y_axis . laxis_override .= axisGridHide
    V.forM_ rs $ \r -> plot (line (tool r) [ zip depths (map LogValue $ times r) ] )
