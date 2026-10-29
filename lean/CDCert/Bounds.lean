/-
CDCert.Bounds — **the recurrences for the actual extremal functions** `f` and `h` of Codex's
semantic Condorcet domains (every odd voter profile has a transitive majority).

* `peakPit_recurrence : 3 h(n+1) ≤ 8 h(n)` (Theorem `thm:main`, `(eq:peak)` first part): a largest
  peak-pit domain is full under extreme laws (Codex's `maximum_peakPit_fullClass`), so it lies in
  `InF`, and `InF.density` gives `3 (n+1) |D| ≤ 8 del(D) ≤ 8 (n+1) h(n)`.
* `h_geometric : 3^(n-3) h(n) ≤ 4 · 8^(n-3)` for `n ≥ 3`, i.e. `h(n) ≤ 4 (8/3)^(n-3)`, from
  `h(3) = 4` (Codex's `h_three`).
* `general_step_of_free_le_locked`: for a domain attaining `f(n+1)` whose free pairs inject into
  its locked letters (Proposition `prop:free`, proved in `CDCert.FreeLocked`; an explicit
  parameter in this helper), `(11(n+1) + 8) f(n+1) ≤ 32 (n+1) f(n)`. This combines Codex's component identity
  `Σ_K del(K) = del(D) + G(D)`, the components lying in `InF`, `InF.density` on every component and
  Codex's reduction `gap_bound_of_free_le_locked`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.BridgeK6
import Condorcet.BaseThree
import Condorcet.GapCounts
import Condorcet.ComponentCounting
import Condorcet.SlotAdjacency
import Condorcet.FullDomains

namespace CDCert.Bounds

open Condorcet

/-! ### Peak-pit domains -/

/-- **The peak-pit recurrence** `3 h(n + 1) ≤ 8 h(n)`, for every `n`. -/
theorem peakPit_recurrence (n : Nat) : 3 * h (n + 1) ≤ 8 * h n := by
  obtain ⟨D, hD, hcard⟩ := exists_maximum_peakPit (n + 1)
  rcases D.eq_empty_or_nonempty with hE | hne
  · rw [← hcard, hE]; simp
  have hF : InF D := ⟨hne, maximum_peakPit_fullClass hD hcard⟩
  have h1 := CDCert.Bridge.InF.density hF
  have h2 := deletionSum_le_peakPit hD
  rw [hcard] at h1
  have h3 : (n + 1) * (3 * h (n + 1)) ≤ (n + 1) * (8 * h n) := by
    calc (n + 1) * (3 * h (n + 1)) = 3 * (n + 1) * h (n + 1) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (n + 1) 3]
      _ ≤ 8 * deletionSum D := h1
      _ ≤ 8 * ((n + 1) * h n) := Nat.mul_le_mul_left 8 h2
      _ = (n + 1) * (8 * h n) := by
            rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 8 (n + 1)]
  exact Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos n)

/-- The paper's form: `3 h(n) ≤ 8 h(n - 1)` for `n ≥ 1`. -/
theorem peakPit_recurrence' {n : Nat} (hn : 1 ≤ n) : 3 * h n ≤ 8 * h (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using peakPit_recurrence k

/-- **Geometric peak-pit bound**: `3^(n-3) h(n) ≤ 4 · 8^(n-3)` for `n ≥ 3`. -/
theorem h_geometric {n : Nat} (hn : 3 ≤ n) : 3 ^ (n - 3) * h n ≤ 4 * 8 ^ (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel_left]
  clear hn
  induction k with
  | zero => simp [h_three]
  | succ k ih =>
    have hr := peakPit_recurrence (3 + k)
    rw [show 3 + (k + 1) = 3 + k + 1 by omega]
    calc 3 ^ (k + 1) * h (3 + k + 1) = 3 ^ k * (3 * h (3 + k + 1)) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 3 ^ k * (8 * h (3 + k)) := Nat.mul_le_mul_left _ hr
      _ = 8 * (3 ^ k * h (3 + k)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ k) 8, Nat.mul_assoc]
      _ ≤ 8 * (4 * 8 ^ k) := Nat.mul_le_mul_left 8 ih
      _ = 4 * 8 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 8 (8 ^ k)]

/-! ### General Condorcet domains: a helper interface discharged in Recurrences -/

/-- **The general recurrence, given the free-to-locked injection for a maximum domain.**
For a Condorcet domain `D` on `n + 1` alternatives with `|D| = f(n + 1)` and
`freeCount D ≤ lockedCount D`, `(11 (n + 1) + 8) f(n + 1) ≤ 32 (n + 1) f(n)`. -/
theorem general_step_of_free_le_locked {n : Nat} {D : Domain (Fin (n + 1))} (hD : IsCondorcet D)
    (hcard : D.card = f (n + 1)) (hinj : freeCount D ≤ lockedCount D) :
    (11 * (n + 1) + 8) * f (n + 1) ≤ 32 * (n + 1) * f n := by
  classical
  have hfull : IsFull D := (maximum_isMaximal hD hcard).isFull
  have hgap := hfull.gap_bound_of_free_le_locked hinj
  have hcomp := hfull.sum_components_deletionSum
  have hcards := sum_components_card D
  have hdens : ∑ K ∈ components D, 3 * (n + 1) * K.card ≤ ∑ K ∈ components D, 8 * deletionSum K :=
    Finset.sum_le_sum (fun K hK => CDCert.Bridge.InF.density (hfull.components_inF hK))
  rw [← Finset.mul_sum, ← Finset.mul_sum, hcards, hcomp] at hdens
  have hdel := deletionSum_le_general hD
  rw [hcard] at hdens hgap
  -- linear arithmetic in the atoms `a = (n+1) f(n+1)`, `b = (n+1) f(n)`
  have e1 : 3 * (n + 1) * f (n + 1) = 3 * ((n + 1) * f (n + 1)) := Nat.mul_assoc _ _ _
  have e2 : (n + 2) * f (n + 1) = (n + 1) * f (n + 1) + f (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
  have e3 : (11 * (n + 1) + 8) * f (n + 1) = 11 * ((n + 1) * f (n + 1)) + 8 * f (n + 1) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have e4 : 32 * (n + 1) * f n = 32 * ((n + 1) * f n) := Nat.mul_assoc _ _ _
  rw [e1] at hdens
  rw [e2] at hgap
  rw [e3, e4]
  omega

/-- **The free-to-locked injection** (Proposition `prop:free`) for maximal Condorcet domains on at
least three alternatives, in Codex's counts. The helpers below take this proposition as a
parameter; CDCert.Recurrences.freeLockedInjection proves it using CDCert.FreeLocked.free_le_locked. -/
def FreeLockedInjection : Prop :=
  ∀ (n : Nat), 2 ≤ n → ∀ D : Domain (Fin (n + 1)), IsMaximal D → freeCount D ≤ lockedCount D

/-- **The general recurrence** `(11 (n + 1) + 8) f(n + 1) ≤ 32 (n + 1) f(n)`, `n + 1 ≥ 3`, from the
injection. -/
theorem general_recurrence_of_injection (hinj : FreeLockedInjection) {n : Nat} (hn : 2 ≤ n) :
    (11 * (n + 1) + 8) * f (n + 1) ≤ 32 * (n + 1) * f n := by
  obtain ⟨D, hD, hcard⟩ := exists_maximum_general (n + 1)
  exact general_step_of_free_le_locked hD hcard (hinj n hn D (maximum_isMaximal hD hcard))

/-- **Geometric general bound** `11^(n-3) f(n) ≤ 4 · 32^(n-3)`, `n ≥ 3`, from the injection. -/
theorem f_geometric_of_injection (hinj : FreeLockedInjection) {n : Nat} (hn : 3 ≤ n) :
    11 ^ (n - 3) * f n ≤ 4 * 32 ^ (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel_left]
  clear hn
  induction k with
  | zero => simp [f_three]
  | succ k ih =>
    have hr := general_recurrence_of_injection hinj (n := 3 + k) (by omega)
    have hr' : 11 * f (3 + k + 1) ≤ 32 * f (3 + k) := by
      have h1 : (3 + k + 1) * (11 * f (3 + k + 1)) ≤ (3 + k + 1) * (32 * f (3 + k)) := by
        rw [Nat.mul_left_comm (3 + k + 1) 11, Nat.mul_left_comm (3 + k + 1) 32]
        rw [Nat.add_mul, Nat.mul_assoc 11, Nat.mul_assoc 32] at hr
        omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    rw [show 3 + (k + 1) = 3 + k + 1 by omega]
    calc 11 ^ (k + 1) * f (3 + k + 1) = 11 ^ k * (11 * f (3 + k + 1)) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 11 ^ k * (32 * f (3 + k)) := Nat.mul_le_mul_left _ hr'
      _ = 32 * (11 ^ k * f (3 + k)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (11 ^ k) 32, Nat.mul_assoc]
      _ ≤ 32 * (4 * 32 ^ k) := Nat.mul_le_mul_left 32 ih
      _ = 4 * 32 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 32 (32 ^ k)]

end CDCert.Bounds
