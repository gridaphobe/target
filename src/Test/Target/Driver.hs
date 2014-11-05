{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Test.Target.Driver where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Catch             as Ex
import           Control.Monad.State
import qualified Data.HashMap.Strict             as M
import qualified Data.HashSet                    as S
import           Data.List                       hiding (sort)
import           Data.Monoid
import qualified Data.Text                       as T
import           Data.Text.Format
import qualified Data.Text.Lazy                  as LT
import qualified Data.Vector                     as V
import           System.FilePath
import           System.IO.Unsafe
import           Text.Printf

import           Language.Fixpoint.Config        (SMTSolver (..))
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types   hiding (Result (..), env, var)

import           Test.Target.Expr
import           Test.Target.Gen
import           Test.Target.Types
import           Test.Target.Util


reaches :: Symbol
        -> M.HashMap Symbol Value
        -> V.Vector (Symbol, Symbol)
        -> V.Vector (Symbol, Value)
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


allSat :: [Symbol] -> Gen [[Value]]
allSat roots = {-# SCC "allSat" #-} setup >>= io . go
  where
    setup = {-# SCC "allSat.setup" #-} do
       ctx <- gets smtContext
       emb <- gets embEnv
       -- declare sorts
       ss  <- S.toList <$> gets sorts
       let defSort b e = io $ smtWrite ctx (format "(define-sort {} () {})" (b,e))
       -- FIXME: combine this with the code in `fresh`
       forM_ ss $ \case
         FObj "Int" -> return ()
         FInt       -> return ()
         FObj "GHC.Types.Bool"   -> defSort ("GHC.Types.Bool" :: T.Text) ("Bool" :: T.Text)
         FObj "CHOICE" -> defSort ("CHOICE" :: T.Text) ("Bool" :: T.Text)
         s        -> defSort (smt2 s) ("Int" :: T.Text)
       -- declare constructors
       cts <- gets constructors
       mapM_ (\ (c,t) -> io . command ctx $ makeDecl (symbol c) t) cts
       let nullary = [var c | (c,t) <- cts, not (func t)]
       unless (null nullary) $
         void $ io $ command ctx $ Distinct nullary
       -- declare variables
       vs <- gets variables
       mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (arrowize $ snd x)) vs
       -- declare measures
       ms <- gets measEnv
       mapM_ (\m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort emb $ sort m)) ms
       -- assert constraints
       cs <- gets constraints
       --mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
       --                 io . command ctx $ Assert (Just i) c})
       --  cs
       mapM_ (\c -> io . command ctx $ Assert Nothing c) cs
       deps <- V.fromList . map (symbol *** symbol) <$> gets deps
       -- io $ generateDepGraph "deps" deps cs
       return (ctx,vs,deps)

    go :: (Context, [Variable], V.Vector (Symbol,Symbol)) -> IO [[Value]]
    go (!ctx,!vs,!deps) = {-# SCC "allSat.go" #-} do
       real <- gets realized
       modify $ \s@(GS {..}) -> s { realized = [] }
       unless (null real) $
         command ctx $ Assert Nothing $ PNot $ pAnd cs
       resp <- command ctx CheckSat
       case resp of
         Error e -> Ex.throwM $ SmtError (T.unpack e)
         Unsat   -> return []
         Sat     -> do
           -- let real = [v | (v,t) <- vs, t `elem` interps]
           -- Values model <- {-# SCC "allSat.go.GetValue" #-}
           --   if null real
           --   then return $ Values []
           --   else ensureValues $ command ctx (GetValue real)
           -- -- print model
           -- let cs = V.toList $ refute roots (M.fromList model) deps vs
           -- -- i <- gets seed
           -- -- modify $ \s@(GS {..}) -> s { seed = seed + 1 }
           (map snd model:) <$> unsafeInterleaveIO (command ctx (Assert Nothing $ PNot $ pAnd cs) >> go (ctx,vs,deps))

    -- ints vs = S.fromList [symbol v | (v,t) <- vs, t `elem` interps]
    -- interps = [FInt, boolsort, choicesort]
    -- refute !roots !model !deps !vs
    --   = {-# SCC "refute" #-} V.map    (\(x,v) -> var x `eq` ESym (SL v))
    --   . V.filter (\(x,v) -> x `S.member` ints vs)
    --   $ realized
    --   where
    --     realized = {-# SCC "realized" #-} V.concat $ map (\root -> reaches root model deps) roots

generateDepGraph :: String -> V.Vector (Symbol,Symbol) -> Targetablet -> IO ()
generateDepGraph name deps constraints = writeFile (name <.> "dot") digraph
  where
    digraph = unlines $ ["digraph G {"] ++ edges ++ ["}"]
    edges   = [ printf "\"%s\" -> \"%s\" [label=\"%s\"];" (symbolString p) (symbolString c) cs
              | (p, c) <- V.toList deps
              , let cs = intercalate "\\n" [ LT.unpack (smt2 p)
                                           | PImp (PBexp (EVar a)) p <- constraints
                                           , a == c]
              ]


makeDecl :: Symbol -> Sort -> Command
-- FIXME: hack..
makeDecl x _ | x `M.member` smt_set_funs = Assert Nothing PTrue
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

func (FFunc _ _) = True
func _           = False
