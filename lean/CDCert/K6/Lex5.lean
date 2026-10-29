/-
CDCert.K6.Lex5 — list-level groups for the five-level coverage check.

* `groupsPF5`: the options introduced with label 4, pair groups first
  (`pairOptions a 4`, `a < 4`), then the triple groups of `groupsNew 4`
  (extreme laws on `(a, b, 4)`, `a < b < 4`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-- The options introduced with label 4, pair groups first. -/
def groupsPF5 : List (Group (List Nat)) :=
  (List.range 4).map (fun a => pairOptions a 4) ++
  (newTriples 4).map (fun t => lawsExtreme.map (holdsL t.1 t.2.1 t.2.2))

/-- Swap the entries at positions `j` and `j + 1`. -/
def swapAt (j : Nat) (M : List Nat) : List Nat :=
  (M.set j (M.getD (j + 1) 0)).set (j + 1) (M.getD j 0)

end CDCert.K6
