/-
CDCert.ExamplesBits — regression examples for the bitset layer, proved by
`decide` (kernel evaluation, no `native_decide`) and pushed through the
transfer theorems to statements about every defined domain.

Results (n = 4, orders as lists, triples with never-condition options):
* `pp4_card_le_nine`: every domain defined by peak-pit never conditions has at
  most 9 orders (1,296 leaves);
* `all4_card_le_nine`: the same for all nine never conditions (6,561 leaves);
* `pp4_exact_card_le_nine`: every peak-pit defined domain whose top-3 slice is
  exactly `S4` has at most 9 orders, via required-slice filtering, bit-level
  pruning and exact-slice transfer.

This module tests the bitset machinery. The semantic bridge and
never-condition characterisation are supplied in CDCert.Bridge and
Condorcet.TripleCharacterization; the full bounds are stated in CDCert.Main.

`decide +kernel` is used for the heavy checks: it produces the same proof term
as `decide` (`of_decide_eq_true (Eq.refl true)`), checked by the kernel, but
skips the elaborator's slower pre-evaluation. It does not use the compiler.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.Bitset
import CDCert.Examples

namespace CDCert.ExamplesBits

open CDCert CDCert.Bits CDCert.Examples

set_option maxRecDepth 100000

theorem orders4_nodup : (orders 4).Nodup := by decide
theorem orders4_length : (orders 4).length = 24 := by decide

/-- Leaf test: at most `b` orders. -/
def atMost (b : Nat) (m : Nat) : Bool := Nat.ble (countBits 24 m) b

theorem atMost_sound (b : Nat) (m : Nat) (h : atMost b m = true) :
    (decode (orders 4) m).length ≤ b := by
  rw [length_decode, orders4_length]
  exact Nat.le_of_ble_eq_true h

theorem pp4_card_le_nine :
    ∀ c, IsChoice c (groupsPP 4) → (domainOf (orders 4) c).length ≤ 9 :=
  coverage_of_dfsCheckB_noPrune (groupsPP 4) (atMost 9) (fun D => D.length ≤ 9)
    (atMost_sound 9) (by decide +kernel)

theorem all4_card_le_nine :
    ∀ c, IsChoice c (groupsAll 4) → (domainOf (orders 4) c).length ≤ 9 :=
  coverage_of_dfsCheckB_noPrune (groupsAll 4) (atMost 9) (fun D => D.length ≤ 9)
    (atMost_sound 9) (by decide +kernel)

theorem S4_sub_base : ∀ s, s ∈ S4 → s ∈ orders 4 := by decide
theorem S4_sub_top3 : ∀ s, s ∈ S4 → topIs 3 s = true := by decide

theorem pp4_exact_card_le_nine :
    ∀ c, IsChoice c (groupsPP 4) → ExactSlice (topIs 3) S4 (domainOf (orders 4) c) →
      (domainOf (orders 4) c).length ≤ 9 :=
  coverage_of_dfsCheckB orders4_nodup (groupsPP 4) (topIs 3) S4 S4_sub_base S4_sub_top3
    (atMost 9) (fun D => D.length ≤ 9) (atMost_sound 9) (by decide +kernel)

/-- The maximum 9 is attained with exact slice `S4` (list level, plain `decide`). -/
example : ∃ D, D ∈ enumerateExact (topIs 3) S4 (groupsPP 4) (orders 4) ∧ D.length = 9 := by
  decide

end CDCert.ExamplesBits
