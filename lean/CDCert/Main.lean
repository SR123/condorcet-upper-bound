/-
CDCert.Main — **Theorem `thm:main` of Moros–Riis**, for the actual extremal functions of Codex's
semantic Condorcet domains (`Condorcet.f n`: the largest `D : Finset (Order (Fin n))` such that every
odd voter profile from `D` has a transitive majority relation; `Condorcet.h n`: the same for
peak-pit domains, which also satisfy an extreme never-condition on every triple).

For `n ≥ 3`:

* `f(n) ≤ 32n/(11n+8) f(n-1)` and `f(n) ≤ 4 (32/11)^(n-3)`;
* `h(n) ≤ (8/3) h(n-1)` and `h(n) ≤ 4 (8/3)^(n-3)`;
* the limits of `f(n)^(1/n)` and `h(n)^(1/n)` exist and are at most `32/11` and `8/3`;
* `f(n) = O(n^(-8/11) (32/11)^n)`.

This file only restates the results proved in `CDCert.Recurrences` and `CDCert.Asymptotics`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Asymptotics

namespace CDCert.Main

open Condorcet Filter Topology

/-- `(eq:general)`, the recurrence: `(11n + 8) f(n) ≤ 32 n f(n − 1)`. -/
theorem general_recurrence {n : ℕ} (hn : 3 ≤ n) : (11 * n + 8) * f n ≤ 32 * n * f (n - 1) :=
  CDCert.Recurrences.general_recurrence' (by omega)

/-- `(eq:general)`, the geometric bound: `f(n) ≤ 4 (32/11)^(n-3)`. -/
theorem general_geometric {n : ℕ} (hn : 3 ≤ n) : (f n : ℝ) ≤ 4 * (32 / 11 : ℝ) ^ (n - 3) :=
  CDCert.Asymptotics.f_le_real hn

/-- `(eq:peak)`, the recurrence: `3 h(n) ≤ 8 h(n − 1)`. -/
theorem peak_recurrence {n : ℕ} (hn : 3 ≤ n) : 3 * h n ≤ 8 * h (n - 1) :=
  CDCert.Recurrences.peakPit_recurrence (by omega)

/-- `(eq:peak)`, the geometric bound: `h(n) ≤ 4 (8/3)^(n-3)`. -/
theorem peak_geometric {n : ℕ} (hn : 3 ≤ n) : (h n : ℝ) ≤ 4 * (8 / 3 : ℝ) ^ (n - 3) :=
  CDCert.Asymptotics.h_le_real hn

/-- The limit of `f(n)^(1/n)` exists and is at most `32/11`. -/
theorem general_limit :
    ∃ L, Tendsto (fun n : ℕ => (f n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧ L ≤ 32 / 11 :=
  CDCert.Asymptotics.f_root_limit

/-- The limit of `h(n)^(1/n)` exists and is at most `8/3`. -/
theorem peak_limit :
    ∃ L, Tendsto (fun n : ℕ => (h n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧ L ≤ 8 / 3 :=
  CDCert.Asymptotics.h_root_limit

/-- The polynomial correction: `f(n) = O(n^(-8/11) (32/11)^n)`. -/
theorem general_polynomial_correction :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(8 / 11 : ℝ)) * (32 / 11 : ℝ) ^ n) :=
  CDCert.Asymptotics.f_isBigO

end CDCert.Main
