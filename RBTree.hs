{-@ LIQUID "-g-package-db" @-}
{-@ LIQUID "-g.cabal-sandbox/x86_64-osx-ghc-7.6.3-packages.conf.d" @-}
{-@ LIQUID "-g-no-user-package-db" @-}


{-@ LIQUID "--no-termination"   @-}

module Main where

import Data.Monoid
import Data.Proxy
import LiquidSMT hiding (Tree(..), gen_leaf, stitch_leaf, gen_node, stitch_node)
import Language.Fixpoint.Types (stringSymbol, Sort(..), toReft)
import Language.Haskell.Liquid.Types (RType(..))

import Debug.Trace

import Language.Haskell.Liquid.Prelude hiding (eq)

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)
              deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ add :: (Ord a) => a -> RBT a -> RBT a @-}
add x s = makeBlack (ins x s)

{-@ ins :: (Ord a) => a -> t:RBT a -> {v: ARBTN a {(bh t)} | ((IsB t) => (isRB v))} @-}
ins kx Leaf             = Node R kx Leaf Leaf
ins kx s@(Node B x l r) = case compare kx x of
                            LT -> let t = lbal x (ins kx l) r in t 
                            GT -> let t = rbal x l (ins kx r) in t 
                            EQ -> s
ins kx s@(Node R x l r) = case compare kx x of
                            LT -> Node R x (ins kx l) r
                            GT -> Node R x l (ins kx r)
                            EQ -> s

---------------------------------------------------------------------------
-- | Delete an element ----------------------------------------------------
---------------------------------------------------------------------------

{-@ remove :: (Ord a) => a -> RBT a -> RBT a @-}
remove x t = makeBlack (del x t)

{-@ predicate HDel T V = (bh V) = (if (isB T) then (bh T) - 1 else (bh T)) @-}

{-@ del              :: (Ord a) => a -> t:RBT a -> {v:ARBT a | ((HDel t v) && ((isB t) || (isRB v)))} @-}
del x Leaf           = Leaf
del x (Node _ y a b) = case compare x y of
   EQ -> append y a b 
   LT -> case a of
           Leaf         -> Node R y Leaf b
           Node B _ _ _ -> lbalS y (del x a) b
           _            -> let t = Node R y (del x a) b in t 
   GT -> case b of
           Leaf         -> Node R y a Leaf 
           Node B _ _ _ -> rbalS y a (del x b)
           _            -> Node R y a (del x b)

{-@ append                                  :: y:a -> l:RBT {v:a | v < y} -> r:RBTN {v:a | y < v} {(bh l)} -> (ARBT2 a l r) @-}
append :: a -> RBTree a -> RBTree a -> RBTree a
append _ Leaf r                               = r
append _ l Leaf                               = l
append piv (Node R lx ll lr) (Node R rx rl rr)  = case append piv lr rl of 
                                                    Node R x lr' rl' -> Node R x (Node R lx ll lr') (Node R rx rl' rr)
                                                    lrl              -> Node R lx ll (Node R rx lrl rr)
append piv (Node B lx ll lr) (Node B rx rl rr)  = case append piv lr rl of 
                                                    Node R x lr' rl' -> Node R x (Node B lx ll lr') (Node B rx rl' rr)
                                                    lrl              -> lbalS lx ll (Node B rx lrl rr)
append piv l@(Node B _ _ _) (Node R rx rl rr)   = Node R rx (append piv l rl) rr
append piv l@(Node R lx ll lr) r@(Node B _ _ _) = Node R lx ll (append piv lr r)

---------------------------------------------------------------------------
-- | Delete Minimum Element -----------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin            :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ x l r) = makeBlack t
  where 
    (_, t)               = deleteMin' x l r


{-@ deleteMin'                   :: k:a -> l:RBT {v:a | v < k} -> r:RBTN {v:a | k < v} {(bh l)} -> (a, ARBT2 a l r) @-}
deleteMin' k Leaf r              = (k, r)
deleteMin' x (Node R lx ll lr) r = (k, Node R x l' r)   where (k, l') = deleteMin' lx ll lr 
deleteMin' x (Node B lx ll lr) r = (k, lbalS x l' r )   where (k, l') = deleteMin' lx ll lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

{-@ lbalS                             :: k:a -> l:ARBT {v:a | v < k} -> r:RBTN {v:a | k < v} {1 + (bh l)} -> {v: ARBTN a {1 + (bh l)} | ((IsB r) => (isRB v))} @-}
lbalS k (Node R x a b) r              = Node R k (Node B x a b) r
lbalS k l (Node B y a b)              = let t = rbal k l (Node R y a b) in t 
lbalS k l (Node R z (Node B y a b) c) = Node R y (Node B k l a) (rbal z b (makeRed c))
lbalS k l r                           = liquidError "nein" -- Node R l k r

{-@ rbalS                             :: k:a -> l:RBT {v:a | v < k} -> r:ARBTN {v:a | k < v} {(bh l) - 1} -> {v: ARBTN a {(bh l)} | ((IsB l) => (isRB v))} @-}
rbalS k l (Node R y b c)              = Node R k l (Node B y b c)
rbalS k (Node B x a b) r              = let t = lbal k (Node R x a b) r in t 
rbalS k (Node R x a (Node B y b c)) r = Node R y (lbal x (makeRed a) b) (Node B k c r)
rbalS k l r                           = liquidError "nein" -- Node R l k r

{-@ lbal                              :: k:a -> l:ARBT {v:a | v < k} -> RBTN {v:a | k < v} {(bh l)} -> RBTN a {1 + (bh l)} @-}
lbal k (Node R y (Node R x a b) c) r  = Node R y (Node B x a b) (Node B k c r)
lbal k (Node R x a (Node R y b c)) r  = Node R y (Node B x a b) (Node B k c r)
lbal k l r                            = Node B k l r

{-@ rbal                              :: k:a -> l:RBT {v:a | v < k} -> ARBTN {v:a | k < v} {(bh l)} -> RBTN a {1 + (bh l)} @-}
rbal x a (Node R y b (Node R z c d))  = Node R y (Node B x a b) (Node B z c d)
rbal x a (Node R z (Node R y b c) d)  = Node R y (Node B x a b) (Node B z c d)
rbal x l r                            = Node B x l r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type BlackRBT a = {v: RBT a | ((IsB v) && (bh v) > 0)} @-}

{-@ makeRed :: l:BlackRBT a -> ARBTN a {(bh l) - 1} @-}
makeRed (Node B x l r) = Node R x l r
makeRed _              = liquidError "nein"

{-@ makeBlack :: ARBT a -> RBT a @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ x l r) = Node B x l r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Ordered Red-Black Trees

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

-- | Red-Black Trees

{-@ type RBT a    = {v: (ORBT a) | ((isRB v) && (isBH v)) } @-}
{-@ type RBTN a N = {v: (RBT a) | (bh v) = N }              @-}

{-@ type ORBTL a X = RBT {v:a | v < X} @-}
{-@ type ORBTG a X = RBT {v:a | X < v} @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c x l r) = ((isRB l) && (isRB r) && (c == R => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a    = {v: (ORBT a) | ((isARB v) && (isBH v))} @-}
{-@ type ARBTN a N = {v: (ARBT a)   | (bh v) = N }             @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c x l r) = ((isRB l) && (isRB r))
  @-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a L R = {v:ARBTN a {(bh L)} | (((IsB L) && (IsB R)) => (isRB v))} @-}

-- | Color of a tree

{-@ measure col         :: RBTree a -> Color
    col (Node c x l r)  = c
    col (Leaf)          = B
  @-}

{-@ measure isB        :: RBTree a -> Prop
    isB (Leaf)         = false
    isB (Node c x l r) = c == B 
  @-}

{-@ predicate IsB T = col(T) == B @-}

-- | Black Height

{-@ measure isBH        :: RBTree a -> Prop
    isBH (Leaf)         = true
    isBH (Node c x l r) = ((isBH l) && (isBH r) && (bh l) = (bh r))
  @-}

{-@ measure bh        :: RBTree a -> Int
    bh (Leaf)         = 0
    bh (Node c x l r) = (bh l) + (if (c == R) then 0 else 1) 
  @-}

-- | Binary Search Ordering

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node (c    :: Color)
                   (key  :: a)
                   (left :: RBTree <l, r> (a <l key>))
                   (left :: RBTree <l, r> (a <r key>))
  @-}

{-@ data Color = B | R @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V) && (Inv3 V))   @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}
{-@ predicate Inv3 V = 0 <= (bh v)                          @-}

{-@ invariant {v: Color | (v == R || v == B)}               @-}

{-@ invariant {v: RBTree a | (Invs v)}                      @-}

{-@ inv            :: RBTree a -> {v:RBTree a | (Invs v)}   @-}
inv Leaf           = Leaf
inv (Node c x l r) = Node c x (inv l) (inv r)

-----------------------------------------------------------

{- LIQUID "--no-termination" @-}

-- module Main where

-- import Data.Monoid
-- import Data.Proxy
-- import LiquidSMT hiding (Tree(..), gen_leaf, stitch_leaf, gen_node, stitch_node)
-- import Language.Fixpoint.Types (stringSymbol, Sort(..), toReft)
-- import Language.Haskell.Liquid.Types (RType(..))

-- import Debug.Trace

-- data RBTree a = Leaf
--               | Node Col !BlackHeight !(RBTree a) a !(RBTree a)
--               deriving (Show)

-- type Col = Int

-- data Color = B -- ^ Black
--            | R -- ^ Red
--            deriving (Eq,Show)

-- type BlackHeight = Int

-- {- invariant {v:Color | (v = B || v = R) } @-}


-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------


-- -- delete :: Ord a => a -> RBTree a -> RBTree a
-- -- delete x t = turnB' s
-- --   where
-- --     (s,_) = delete' x t
-- -- 
-- -- delete' :: Ord a => a -> RBTree a -> RBTreeBDel a
-- -- delete' _ Leaf = (Leaf, False)
-- -- delete' x (Node c h l y r) = case compare x y of
-- --     LT -> let (l',d) = delete' x l
-- --               t = Node c h l' y r
-- --           in if d then unbalancedR c (h-1) l' y r else (t, False)
-- --     GT -> let (r',d) = delete' x r
-- --               t = Node c h l y r'
-- --           in if d then unbalancedL c (h-1) l y r' else (t, False)
-- --     EQ -> case r of
-- --         Leaf -> if c == B then blackify l else (l, False)
-- --         _ -> let ((r',d),m) = deleteMin' r
-- --                  t = Node c h l m r'
-- --              in if d then unbalancedL c (h-1) l m r' else (t, False)


-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------

-- {- x :: RBT Int @-}
-- x :: RBTree Int
-- x = Node 0 0 (Node 1 0 (Node (-1) 0 (Node 1 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf)) 0 (Node 1 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf))) 0 (Node (-1) 0 (Node (-1) 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf)) 0 (Node 1 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf)))) 0 (Node 1 0 (Node 1 0 (Node (-1) 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf)) 0 (Node 1 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf))) 0 (Node 1 0 (Node (-1) 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf)) 0 (Node 1 0 (Node 0 0 Leaf 0 Leaf) 0 (Node 0 0 Leaf 0 Leaf))))

-- {- insert :: Ord a => a -> RBT a -> RBT a @-}
-- --insert :: Ord a => a -> RBTree a -> RBTree a
-- insert kx t = turnB (insert' kx t)

-- {- turnB :: ARBT a -> RBT a @-}
-- --turnB :: RBTree a -> RBTree a
-- turnB Leaf           = error "turnB"
-- turnB (Node _ h l x r) = Node 1 h l x r

-- {- insert' :: Ord a => a -> t:RBT a -> {v: ARBT a | ((IsB t) => (isRB v))} @-}
-- --insert' :: Ord a => a -> RBTree a -> RBTree a
-- insert' kx Leaf = Node 0 1 Leaf kx Leaf
-- insert' kx s@(Node 1 h l x r) = case compare kx x of
--     LT -> let zoo = balanceL' h (insert' kx l) x r in zoo   -- TODO: cf. issue #182
--     GT -> let zoo = balanceR' h l x (insert' kx r) in zoo   -- TODO: cf. issue #182
--     EQ -> s
-- insert' kx s@(Node 0 h l x r) = case compare kx x of
--     LT -> Node 0 h (insert' kx l) x r
--     GT -> Node 0 h l x (insert' kx r)
--     EQ -> s
-- -- insert' kx s = error $ show s

-- {- balanceL' :: Int -> ARBT a -> a -> RBT a -> RBT a @-}
-- balanceL' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
-- balanceL' h (Node 0 _ (Node 0 _ a x b) y c) z d =
--    Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
-- balanceL' h (Node 0 _ a x (Node 0 _ b y c)) z d =
--    Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
-- balanceL' h l x r =  Node 1 h l x r

-- {- balanceR' :: Int -> RBT a -> a -> ARBT a -> RBT a @-}
-- balanceR' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
-- balanceR' h a x (Node 0 _ b y (Node 0 _ c z d)) =
--     Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
-- balanceR' h a x (Node 0 _ (Node 0 _ b y c) z d) =
--     Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
-- balanceR' h l x r = Node 1 h l x r

-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------

-- {- type RBT a  = {v: (RBTree a) | (isRB v)}  @-}

-- {- type ARBT a = {v: (RBTree a) | (isARB v)} @-}

-- {- measure isRB           :: RBTree a -> Prop
--     isRB (Leaf)            = true
--     isRB (Node c h l x r)  = ((RBC c) && (isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
--   @-}

-- isRB Leaf = True
-- isRB (Node c h l x r) = isRB l && isRB r && (c /= 0 || (isB l && isB r))

-- isB Leaf = True
-- isB (Node c _ _ _ _) = c /= 0

-- {- measure isARB          :: (RBTree a) -> Prop
--     isARB (Leaf)           = true
--     isARB (Node c h l x r) = ((isRB l) && (isRB r))
--   @-}

-- {- measure col :: RBTree a -> Col
--     col (Node c h l x r) = c
--     col (Leaf)           = 1
--   @-}

-- {- predicate IsB T = not (Red (col T)) @-}
-- {- predicate Red C = C == 0            @-}
-- {- predicate RBC C = (C == 0 || C == 1)  @-}

-- -------------------------------------------------------------------------------
-- -- Auxiliary Invariants -------------------------------------------------------
-- -------------------------------------------------------------------------------

-- {- invariant {v: RBTree a | ((isRB v) => (isARB v))} @-}

-- {- inv              :: RBTree a -> {v:RBTree a | ((isRB v) => (isARB v)) } @-}
-- inv Leaf             = Leaf
-- inv (Node c h l x r) = Node c h (inv l) x (inv r)


--------------------------------------------------------------------------------
-- Testing ---------------------------------------------------------------------
--------------------------------------------------------------------------------

colorsort = FObj $ stringSymbol "Int"

instance Constrain Color where
  gen _ _ t@(RApp c _ _ r)
    = do bb <- make "Main.B" [] colorsort
         rr <- make "Main.R" [] colorsort
         constrain $ var bb `eq` var "Main.B"
         constrain $ var rr `eq` var "Main.R"
         x <- freshChoose [bb,rr] colorsort
         constrain $ ofReft x (toReft r)
         return x

  stitch _
    = do [r,b] <- popChoices 2
         pop
         rr    <- pop >> return R
         bb    <- pop >> return B
         case (b,r) of
           (True,_) -> return bb
           (_,True) -> return rr

  toExpr B = app (stringSymbol "Main.B") []
  toExpr R = app (stringSymbol "Main.R") []

instance Constrain a => Constrain (RBTree a) where
  -- gen _ _ t | trace (show t) False = undefined
  gen _ 0 t = gen_leaf t
  gen p d t@(RApp c ts ps r)
    = do let t' = RApp c ts ps mempty
         x1 <- gen_leaf t'
         x2 <- gen_node p d t'
         x3 <- freshChoose [x1,x2] treesort
         constrain $ ofReft x3 (toReft r)
         return x3

  stitch 0 = stitch_leaf
  stitch d
    = do [n,l] <- popChoices 2
         pop
         nn    <- stitch_node d
         ll    <- stitch_leaf
         case (l,n) of
           (True,_) -> return ll
           (_,True) -> return nn

  toExpr Leaf           = app (stringSymbol "Main.Leaf") []
  toExpr (Node c x l r) = app (stringSymbol "Main.Node")
                          [ toExpr c, toExpr x, toExpr l, toExpr r]

gen_leaf (RApp _ _ _ _)
  = make "Main.Leaf" [] treesort

stitch_leaf
  = pop >> return Leaf

gen_node p d t@(RApp c ts ps r)
  = make4 "Main.Node" (pc, pa, p, p) t treesort d
  where pc = Proxy :: Proxy Color
        pa = reproxyElem p

stitch_node d
  = apply4 Node d
  -- = do pop
  --      r <- stitch (d-1)
  --      l <- stitch (d-1)
  --      x <- stitch (d-1)
  --      c <- stitch (d-1)
  --      return $ Node c x l r

main = testOne (add :: Int -> RBTree Int -> RBTree Int) "Main.add" "RBTree.hs"
