{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Test.LiquidCheck.Driver where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import           Control.Monad.State
import qualified Data.HashMap.Strict             as M
import qualified Data.HashSet                    as S
import           Data.List                       hiding (sort)
import           Data.Monoid
import           Data.Text.Format
import qualified Data.Text.Lazy                  as T
import qualified Data.Vector                     as V
import           System.FilePath
import           System.IO.Unsafe
import           Text.Printf

import           Language.Fixpoint.Config        (SMTSolver (..))
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types   hiding (Result (..), env, var)

import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


reaches :: Symbol
        -> M.HashMap Symbol String
        -> V.Vector (Symbol, Symbol)
        -> V.Vector (Symbol, String)
reaches root model deps = go root
  where
    go root
      | isChoice && taken
      = (root,val) `V.cons` V.concatMap go (reached deps) -- [r | (x,r) <- deps, x == root]
      | isChoice
      = V.empty -- V.fromList [(root,val)]
      | otherwise
      = (root,val) `V.cons` V.concatMap go (reached deps) -- [r | (x,r) <- deps, x == root]
      where
        val      = model M.! root
        isChoice = "CHOICE" `isPrefixOf` symbolString root
        taken    = val == "true"
        reached  = V.map snd . V.filter ((==root).fst)

allSat :: [Symbol] -> Gen [[String]]
allSat roots = setup >>= io . go
  where
    setup = do
       ctx <- io $ makeContext Z3
       -- declare sorts
       ss  <- S.toList <$> gets sorts
       let defSort b e = io $ smtWrite ctx (format "(define-sort {} () {})" (b,e))
       -- FIXME: combine this with the code in `fresh`
       forM_ ss $ \case
         "Int" -> return ()
         "GHC.Types.Bool"   -> defSort ("GHC.Types.Bool" :: T.Text) ("Bool" :: T.Text)
         "CHOICE" -> defSort ("CHOICE" :: T.Text) ("Bool" :: T.Text)
         s        -> defSort s ("Int" :: T.Text)
       -- declare constructors
       cts <- gets constructors
       mapM_ (\ (c,t) -> io . command ctx $ makeDecl (symbol c) t) cts
       let nullary = [var c | (c,t) <- cts, not (func t)]
       when (not $ null nullary) $
         void $ io $ command ctx $ Distinct nullary
       -- declare variables
       vs <- gets variables
       mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       ms <- gets measEnv
       mapM_ (\m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort mempty $ sort m)) ms
       -- assert constraints
       cs <- gets constraints
       mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
                        io . command ctx $ Assert (Just i) c})
         cs
       deps <- V.fromList . map (symbol *** symbol) <$> gets deps
       -- io $ generateDepGraph "deps" deps cs
       return (ctx,vs,deps)

    go :: (Context, [Variable], V.Vector (Symbol,Symbol)) -> IO [[String]]
    go (ctx,vs,deps) = do
       resp <- command ctx CheckSat
       case resp of
         Error e -> cleanupContext ctx >> error (T.unpack e)
         Unsat   -> cleanupContext ctx >> return []
         Sat     -> unsafeInterleaveIO $ do
           Values model <- command ctx (GetValue [symbol v | (v,t) <- vs, t `elem` interps])
           -- print model
           let cs = V.toList $ refute roots (M.fromList model) deps vs
           -- i <- gets seed
           -- modify $ \s@(GS {..}) -> s { seed = seed + 1 }
           command ctx $ Assert Nothing $ PNot $ pAnd cs
           (map snd model:) <$> go (ctx,vs,deps)

    ints vs = S.fromList [symbol v | (v,t) <- vs, t `elem` interps]
    interps = [FInt, boolsort, choicesort]
    refute roots model deps vs
      = V.map    (\(x,v) -> var x `eq` ESym (SL v))
      . V.filter (\(x,v) -> x `S.member` ints vs)
      $ realized
      where
        realized = V.concat $ map (\root -> reaches root model deps) roots

generateDepGraph :: String -> V.Vector (Symbol,Symbol) -> Constraint -> IO ()
generateDepGraph name deps constraints = writeFile (name <.> "dot") digraph
  where
    digraph = unlines $ ["digraph G {"] ++ edges ++ ["}"]
    edges   = [ printf "\"%s\" -> \"%s\" [label=\"%s\"];" p c cs
              | (S p, S c) <- V.toList deps
              , let cs = intercalate "\\n" [T.unpack (smt2 p) | PImp (PBexp (EVar (S a))) p <- constraints, a == c]
              ]


makeDecl :: Symbol -> Sort -> Command
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

func (FFunc _ _) = True
func _           = False
