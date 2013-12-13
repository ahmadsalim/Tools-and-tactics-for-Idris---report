module DependentTypes

data Balanced1 : Nat -> Nat -> Type where
  RightLeaning : {n : Nat} -> Balanced1 n    (S n)
  Balance      : {n : Nat} -> Balanced1 n     n
  LeftLeaning  : {n : Nat} -> Balanced1 (S n) n

data AVL : Nat -> Type -> Type where
  Leaf : {a : Type} -> AVL Z a
  Node : {a : Type} -> {nl : Nat} -> {nr : Nat}
         -> AVL nl a -> a -> AVL nr a -> Balanced1 nl nr
         -> AVL (S (max nl nr)) a

testAVLCorrect : AVL 2 Nat
testAVLCorrect = Node (Node Leaf 2 Leaf Balance) 1 Leaf LeftLeaning

testAVLIncorrect : AVL 3 Nat
testAVLIncorrect = Node
                      (Node (Node Leaf 3 Leaf Balance) 2 Leaf LeftLeaning)
                      1 Leaf ?no_value_can_be_here
