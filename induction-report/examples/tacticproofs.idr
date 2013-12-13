reflexiveEq : {n : Nat} -> n = n
reflexiveEq = ?reflexiveEqProof

symmetricEq : {n, m : Nat} -> (H : n = m) -> m = n
symmetricEq = ?symmetricEqProof

transitiveEq : {n, m, o : Nat} -> (H1 : n = m) -> (H2 : m = o) -> n = o
transitiveEq = ?transitiveEqProof

---------- Proofs ----------

reflexiveEqProof = proof
  intro n
  trivial

symmetricEqProof = proof
  intro n, m, H
  rewrite H
  trivial

transitiveEqProof = proof
  intro n, m, o, H1, H2
  rewrite (sym H1)
  exact H2
