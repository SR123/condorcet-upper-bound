/-
CDCert.K6.Tree — binary search trees with natural keys and values, with a
lookup written with the recursor for kernel evaluation.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/

namespace CDCert.K6

/-- Binary search tree with natural keys and values. -/
inductive KTree where
  | leaf : KTree
  | node : KTree → Nat → Nat → KTree → KTree

/-- Value stored at key `k`, `0` if absent. -/
noncomputable def KTree.find (t : KTree) (k : Nat) : Nat :=
  KTree.rec (motive := fun _ => Nat) 0
    (fun _ key v _ ihl ihr => cond (Nat.blt k key) ihl (cond (Nat.blt key k) ihr v)) t

end CDCert.K6
