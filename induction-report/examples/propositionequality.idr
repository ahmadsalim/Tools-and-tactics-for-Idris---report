data (=) : a -> b -> Type where
  refl : {x : a} -> x = x

cong : {a : Type} -> {b : Type} -> {x : a} -> {y : a} -> {p : a -> b} 
        -> x = y -> p x = p y
cong refl = refl

npluso : {n : Nat} -> n + Z = n
npluso {n = Z}    = refl
npluso {n = S n}  = cong (npluso {n})
