module RBTreeTest where

import           RBTree

import           Test.Target

type E = Char
type T = RBTree E

liquidTests :: [(String, Test)]
liquidTests = [ ("add",    T (add :: E -> T -> T))
              , ("remove", T (remove :: E -> T -> T))
              ]

liquidTests_bad :: [(String, Test)]
liquidTests_bad = [ ("add",    T (add_bad :: E -> T -> T))
                  , ("remove", T (remove_bad :: E -> T -> T))
                  ]

remove_bad x t = makeBlack (del_bad x t)

del_bad x Leaf           = Leaf
del_bad x (Node _ y a b) = case compare x y of
   EQ -> append_bad y a b
   LT -> case a of
           Leaf         -> Node R y Leaf b
           Node B _ _ _ -> lbalS y (del_bad x a) b
           _            -> let t = Node R y (del_bad x a) b in t
   GT -> case b of
           Leaf         -> Node R y a Leaf
           Node B _ _ _ -> rbalS y a (del_bad x b)
           _            -> Node R y a (del_bad x b)

append_bad :: a -> RBTree a -> RBTree a -> RBTree a
append_bad _ Leaf r                               = r
append_bad _ l Leaf                               = l
append_bad piv (Node R lx ll lr) (Node R rx rl rr)  = case append_bad piv lr rl of
                                                    --Node R x lr' rl' -> Node R x (Node R lx ll lr') (Node R rx rl' rr)
                                                    lrl              -> Node R lx ll (Node R rx lrl rr)
append_bad piv (Node B lx ll lr) (Node B rx rl rr)  = case append_bad piv lr rl of
                                                    --Node R x lr' rl' -> Node R x (Node B lx ll lr') (Node B rx rl' rr)
                                                    lrl              -> lbalS lx ll (Node B rx lrl rr)
append_bad piv l@(Node B _ _ _) (Node R rx rl rr)   = Node R rx (append_bad piv l rl) rr
append_bad piv l@(Node R lx ll lr) r@(Node B _ _ _) = Node R lx ll (append_bad piv lr r)

add_bad x s = ins x s
