/-
CDCert.Recurrences — **the recurrences of Theorem `thm:main`, unconditionally**, for the actual
extremal functions `f`, `h` of Codex's semantic Condorcet domains:

* `gap_inequality` (Theorem `thm:gap`): `G(D) + (n+2)|D| ≤ 3 del(D)` for every maximal Condorcet
  domain on `n + 1` alternatives (Codex's exact slack identity and `CDCert.FreeLocked.free_le_locked`);
* `deletion_lower_bound` (`eq:transfer`): `(11(n+1) + 8)|D| ≤ 32 del(D)` for every maximal `D`;
* `general_recurrence`: `(11(n+1) + 8) f(n+1) ≤ 32 (n+1) f(n)` for every `n`, and the paper's form
  `(11n + 8) f(n) ≤ 32 n f(n-1)` for `n ≥ 1`;
* `f_geometric`: `11^(n-3) f(n) ≤ 4 · 32^(n-3)` for `n ≥ 3`;
* `peakPit_recurrence`, `h_geometric`: `3 h(n) ≤ 8 h(n-1)`, `3^(n-3) h(n) ≤ 4 · 8^(n-3)`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Bounds
import CDCert.FreeLocked

namespace CDCert.Recurrences

open Condorcet

/-- The free-to-locked injection holds for every maximal Condorcet domain. -/
theorem freeLockedInjection : CDCert.Bounds.FreeLockedInjection :=
  fun _ _ _ hD => CDCert.FreeLocked.free_le_locked hD

/-- **Theorem `thm:gap`**: `G(D) ≤ 3 del(D) − (n + 2)|D|` for every maximal Condorcet domain on
`n + 1` alternatives. -/
theorem gap_inequality {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsMaximal D) :
    gapCount D + (n + 2) * D.card ≤ 3 * deletionSum D :=
  hD.isFull.gap_bound_of_free_le_locked (CDCert.FreeLocked.free_le_locked hD)

/-- **`(eq:transfer)`**: `del(D) ≥ (11(n+1) + 8)|D| / 32` for every maximal Condorcet domain on
`n + 1` alternatives. -/
theorem deletion_lower_bound {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsMaximal D) :
    (11 * (n + 1) + 8) * D.card ≤ 32 * deletionSum D := by
  classical
  have hfull : IsFull D := hD.isFull
  have hgap := gap_inequality hD
  have hcomp := hfull.sum_components_deletionSum
  have hcards := sum_components_card D
  have hdens : ∑ K ∈ components D, 3 * (n + 1) * K.card ≤ ∑ K ∈ components D, 8 * deletionSum K :=
    Finset.sum_le_sum (fun K hK => CDCert.Bridge.InF.density (hfull.components_inF hK))
  rw [← Finset.mul_sum, ← Finset.mul_sum, hcards, hcomp] at hdens
  have e1 : 3 * (n + 1) * D.card = 3 * ((n + 1) * D.card) := Nat.mul_assoc _ _ _
  have e2 : (n + 2) * D.card = (n + 1) * D.card + D.card := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
  have e3 : (11 * (n + 1) + 8) * D.card = 11 * ((n + 1) * D.card) + 8 * D.card := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [e1] at hdens
  rw [e2] at hgap
  rw [e3]
  omega

/-- **The general recurrence** `(11(n+1) + 8) f(n+1) ≤ 32 (n+1) f(n)`, for every `n`. -/
theorem general_recurrence (n : Nat) : (11 * (n + 1) + 8) * f (n + 1) ≤ 32 * (n + 1) * f n := by
  obtain ⟨D, hD, hcard⟩ := exists_maximum_general (n + 1)
  exact CDCert.Bounds.general_step_of_free_le_locked hD hcard
    (CDCert.FreeLocked.free_le_locked (maximum_isMaximal hD hcard))

/-- The paper's form: `(11n + 8) f(n) ≤ 32 n f(n − 1)` for `n ≥ 1`. -/
theorem general_recurrence' {n : Nat} (hn : 1 ≤ n) : (11 * n + 8) * f n ≤ 32 * n * f (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using general_recurrence k

/-- **Geometric general bound** `11^(n-3) f(n) ≤ 4 · 32^(n-3)`, i.e. `f(n) ≤ 4 (32/11)^(n-3)`. -/
theorem f_geometric {n : Nat} (hn : 3 ≤ n) : 11 ^ (n - 3) * f n ≤ 4 * 32 ^ (n - 3) :=
  CDCert.Bounds.f_geometric_of_injection freeLockedInjection hn

/-- **The peak-pit recurrence** `3 h(n) ≤ 8 h(n − 1)`, `n ≥ 1`. -/
theorem peakPit_recurrence {n : Nat} (hn : 1 ≤ n) : 3 * h n ≤ 8 * h (n - 1) :=
  CDCert.Bounds.peakPit_recurrence' hn

/-- **Geometric peak-pit bound** `3^(n-3) h(n) ≤ 4 · 8^(n-3)`, i.e. `h(n) ≤ 4 (8/3)^(n-3)`. -/
theorem h_geometric {n : Nat} (hn : 3 ≤ n) : 3 ^ (n - 3) * h n ≤ 4 * 8 ^ (n - 3) :=
  CDCert.Bounds.h_geometric hn

end CDCert.Recurrences
