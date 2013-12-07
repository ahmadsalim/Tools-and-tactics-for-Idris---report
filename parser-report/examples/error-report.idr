module ErrorReport

data List : Type -> Type where
  Nil :: List a
  Cons :: a -> List a -> List a
