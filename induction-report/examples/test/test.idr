module ELIMTest

%elim data  Unit : Type where
  MkUnit : Unit

%elim data  Boolean : Type where
  False : Boolean
  True  : Boolean

%elim data Pair : Type -> Type -> Type where
  MkPair : a -> b -> Pair a b

%elim data  TNat : Type where
  TO : TNat
  TS : TNat -> TNat

infixl 8 +++

(+++) : TNat -> TNat -> TNat
TO +++ m     = m
(TS n) +++ m = TS (n +++ m)

%elim data TList : Type -> Type where
  TNil : TList a
  TCons : a -> TList a -> TList a

infixl 8 @@@
(@@@) : TList a -> TList a -> TList a
TNil          @@@ ys = ys
(TCons x xs)  @@@ ys = TCons x (xs @@@ ys)

%elim data TVect : TNat -> Type -> Type where
  VNil : TVect TO a
  VCons : a -> TVect n a -> TVect (TS n) a

length : (TVect n a) -> TNat
length VNil         = TO
length (VCons x xs) = TS (length xs)

length_proof : (n : TNat) -> (vs : TVect n a) -> (n = length vs)
length_proof {a} n vs = elim_for ELIMTest.TVect a
                        (\m, xs => m = length xs)
                        ?nilCase
                        ?consCase
                        n
                        vs

n_plus_O : (n : TNat) -> (n +++ TO = n)
n_plus_O n = ?npluso_proof

n_plus_S_m : (n : TNat) -> (m : TNat) -> (n +++ TS m = TS (n +++ m))
n_plus_S_m n m = ?nplusSm_proof

plus_commutes : (n : TNat) -> (m : TNat) -> (n +++ m = m +++ n)
plus_commutes n m = ?pluscommutes_proof

%elim data BinaryTree : Type -> Type where
  BLeaf : BinaryTree a
  BNode : BinaryTree a -> a -> BinaryTree a -> BinaryTree a

%elim data WeightedBinaryTree : TNat -> Type -> Type where
  WLeaf : WeightedBinaryTree TO a
  WNode : WeightedBinaryTree n a -> a -> WeightedBinaryTree m a 
          -> WeightedBinaryTree (n +++ m +++ TS TO) a

%elim data Node : Type -> Type where
  Node2 : a -> a -> Node a
  Node3 : a -> a -> a -> Node a

%elim data FingerTree : Type -> Type where
  Empty : FingerTree a
  Single : a -> FingerTree a
  Deep : List a -> FingerTree (Node a) -> List a -> FingerTree a

mutual
  %elim data Even : TNat -> Type where
    evenZero : Even TO
    evenSuc  : Odd n -> Even (TS n)

  %elim data Odd : TNat -> Type where
    oddSuc   : Even n -> Odd (TS n)

mutual
  data FList : Type -> Type where
    FNil  : FList a
    FCons : (x : a) -> (l : FList a) -> {isFresh : fresh x l} -> FList a

  fresh : a -> (FList a) -> Type
  fresh x FNil           = ()
  fresh x (FCons y xs) = ((x = y) -> _|_, fresh x xs)

mirror : BinaryTree a -> BinaryTree a
mirror BLeaf = BLeaf
mirror (BNode l v r) = BNode (mirror r) v (mirror l)

mirror_proof : {a : Type} -> (b : BinaryTree a) -> (b = mirror (mirror b))
mirror_proof {a} b = elim_for ELIMTest.BinaryTree a 
                        (\bb => bb = mirror (mirror bb))
                        ?mirror_leaf_case ?mirror_node_case b

---------- Proofs ----------

ELIMTest.pluscommutes_proof = proof
  intros
  induction n
  compute
  rewrite (n_plus_O m)
  trivial
  intros
  compute
  rewrite (sym iht__0)
  rewrite (n_plus_S_m m t__0)
  trivial


ELIMTest.nplusSm_proof = proof
  intros
  induction n
  compute
  trivial
  intros
  compute
  rewrite iht__0
  trivial


ELIMTest.npluso_proof = proof
  intros
  induction n
  trivial
  intros
  compute
  rewrite iht__0 
  trivial


ELIMTest.mirror_node_case = proof
  compute
  intros
  rewrite ihb__0
  rewrite ihb__1
  trivial


ELIMTest.mirror_leaf_case = proof
  compute
  intros
  trivial

ELIMTest.consCase = proof
  compute
  intros
  rewrite iht__2
  trivial


ELIMTest.nilCase = proof
  compute
  intros
  trivial
