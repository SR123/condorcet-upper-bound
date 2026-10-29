/-
CDCert.Four — list-side facts for four alternatives, stated for the
`HoldsLaw`-shaped groups `groupsFull 4` used by the bridge.

* `full4_card_le_nine`: every domain defined by one law (any of the nine never
  conditions) per increasing triple has at most 9 orders — a kernel bitset
  check (6,561 leaves) transferred by `coverage_of_dfsCheckB_noPrune`;
* `fish4_length`: the selection "middle element never first if it is odd,
  never last if it is even" (Fishburn's alternating scheme) defines a domain
  with exactly 9 orders.

Together with `CDCert.Bridge` and Codex's semantic modules these give
`f 4 = 9` (see `CDCert/Bridge.lean`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`
(`decide +kernel` is kernel evaluation of the same `decide` proof term).
-/
import CDCert.ListOrders
import CDCert.ExamplesBits

namespace CDCert.Four

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder CDCert.ExamplesBits

set_option maxRecDepth 100000

theorem full4_card_le_nine :
    ∀ c, IsChoice c (groupsFull 4) → (domainOf (orders 4) c).length ≤ 9 :=
  coverage_of_dfsCheckB_noPrune (groupsFull 4) (atMost 9) (fun D => D.length ≤ 9)
    (atMost_sound 9) (by decide +kernel)

/-- Fishburn's alternating scheme: on `a < b < c` the middle element `b` is
never first (law `(1,0)`) when `b` is odd, never last (law `(1,2)`) when even. -/
def fishLaw (t : Nat × Nat × Nat) : Fin 3 × Fin 3 :=
  if t.2.1 % 2 = 1 then (1, 0) else (1, 2)

def fishChoice (n : Nat) : List (Opt (List Nat)) :=
  (triplesN n).map fun t => holdsL t.1 t.2.1 t.2.2 (fishLaw t)

theorem fish4_length : (domainOf (orders 4) (fishChoice 4)).length = 9 := by decide

end CDCert.Four
