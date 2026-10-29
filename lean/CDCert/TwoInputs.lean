/-
CDCert.TwoInputs — **the two inputs `(eq:twoinputs)` and the transfer `(eq:transfer)`** of the
paper, stated literally for Codex's actual domains on `n + 1` alternatives (`M = |D|`):

* `first_input` (Theorem `thm:gap`): `G(D) ≤ 3 del(D) − (n + 2) M` for every maximal Condorcet domain;
* `second_input` (Lemma `lem:components` with Proposition `prop:density`):
  `del(D) + G(D) ≥ (3/8)(n + 1) M` for every full domain;
* `transfer`: `del(D) ≥ ((11 (n + 1) + 8)/32) M` for every maximal Condorcet domain.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Recurrences

namespace CDCert.TwoInputs

open Condorcet

/-- **First input** (Theorem `thm:gap`): `G(D) + (n + 2)|D| ≤ 3 del(D)` for maximal `D`. -/
theorem first_input {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsMaximal D) :
    gapCount D + (n + 2) * D.card ≤ 3 * deletionSum D :=
  CDCert.Recurrences.gap_inequality hD

/-- **Second input**: `3 (n + 1) |D| ≤ 8 (del(D) + G(D))` for every full domain `D`. -/
theorem second_input {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsFull D) :
    3 * (n + 1) * D.card ≤ 8 * (deletionSum D + gapCount D) := by
  classical
  have hcomp := hD.sum_components_deletionSum
  have hcards := sum_components_card D
  have hdens : ∑ K ∈ components D, 3 * (n + 1) * K.card ≤ ∑ K ∈ components D, 8 * deletionSum K :=
    Finset.sum_le_sum (fun K hK => CDCert.Bridge.InF.density (hD.components_inF hK))
  rw [← Finset.mul_sum, ← Finset.mul_sum, hcards, hcomp] at hdens
  exact hdens

/-- **Transfer** `(eq:transfer)`: `(11 (n + 1) + 8)|D| ≤ 32 del(D)` for maximal `D`. -/
theorem transfer {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsMaximal D) :
    (11 * (n + 1) + 8) * D.card ≤ 32 * deletionSum D :=
  CDCert.Recurrences.deletion_lower_bound hD

end CDCert.TwoInputs
