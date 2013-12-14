elim_vect : (a : Type) -> (P : (n : Nat) -> (xs : Vect n a) -> Type)
            -> P Z Nil
            -> ((n : Nat) -> (x : a) -> (xs : Vect n a) -> P n xs -> P (S n) (x :: xs))
            -> (m : Nat) -> (ys : Vect m a)
            -> (P m ys)
elim_vect a p pnil pcons Z     Nil     = pnil
elim_vect a p pnil pcons (S n) (x::xs) = pcons n x xs
                                          (elim_vect a p pnil pcons n xs)
