data N =
    zer
  | suc N

add : N -> N -> N
add zer     m = m
add (suc n) m = suc (add n m)

infix 8 ***

data (***) : (a : Type) -> (b : a -> Type) -> Type where
  exists : {a : Type} -> {b : a -> Type} -> (w : a) -> (p : b w) -> a *** b

infixr 5 :::

data Vector : (n : N) -> (a : Type) -> Type where
  nil   : {a : Type}                               -> Vector zer a
  (:::) : {n : N} -> {a : Type} -> a -> Vector n a -> Vector (suc n) a

take_while : (p : a ->  Bool) -> Vector n a -> N *** (\ m => Vector m a)
take_while p nil       = exists zer nil
take_while p (x ::: xs) with (take_while p xs)
  | exists p ys = if p x then exists (suc m) (x ::: ys) else eps
  where eps = exists zer nil


syntax take' [vect] as {x} while [body] = take_while (\x => body) vect
syntax "∃" {x} "->" [ty] = _ *** (\x => ty)

isEven : N -> Bool
isEven zer     = True
isEven (suc x) with (isEven x)
  | True  = False
  | False = True

testSyntax : ∃ m -> Vector m N
testSyntax = take' suc (suc zer) ::: zer ::: suc zer ::: nil as i while isEven i
