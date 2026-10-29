/-
CDCert.Asymptotics — **the geometric and asymptotic corollaries** of Theorem `thm:main` for the
actual extremal functions `f`, `h`.

* `h_le_real : h(n) ≤ 4 (8/3)^(n-3)`, `f_le_real : f(n) ≤ 4 (32/11)^(n-3)` (`n ≥ 3`);
* `h_root_limit : ∃ L, h(n)^(1/n) → L ∧ L ≤ 8/3` and `f_root_limit : ∃ L, f(n)^(1/n) → L ∧
  L ≤ 32/11` (Fekete's lemma for `log h`, `log f`, which are superadditive by ordered
  concatenation, `CDCert.Supermult.h_supermul`, `f_supermul`);
* `f_isBigO : f(n) = O(n^(-8/11) (32/11)^n)` (an induction with the weight `(n+1)^(8/11)` and
  Bernoulli's inequality `(1 + 1/(n+1))^(8/11) ≤ 1 + (8/11)/(n+1)`, from `general_recurrence`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Recurrences
import CDCert.Supermult
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Asymptotics.Defs

namespace CDCert.Asymptotics

open Condorcet Filter Topology Real

/-! ### Geometric bounds over the reals -/

theorem h_le_real {n : Nat} (hn : 3 ≤ n) : (h n : ℝ) ≤ 4 * (8 / 3 : ℝ) ^ (n - 3) := by
  have H := CDCert.Recurrences.h_geometric hn
  have H' : ((3 : ℝ) ^ (n - 3)) * (h n : ℝ) ≤ 4 * (8 : ℝ) ^ (n - 3) := by exact_mod_cast H
  have hpos : (0 : ℝ) < 3 ^ (n - 3) := by positivity
  rw [div_pow, mul_div_assoc', le_div_iff₀ hpos, mul_comm (h n : ℝ)]
  exact H'

theorem f_le_real {n : Nat} (hn : 3 ≤ n) : (f n : ℝ) ≤ 4 * (32 / 11 : ℝ) ^ (n - 3) := by
  have H := CDCert.Recurrences.f_geometric hn
  have H' : ((11 : ℝ) ^ (n - 3)) * (f n : ℝ) ≤ 4 * (32 : ℝ) ^ (n - 3) := by exact_mod_cast H
  have hpos : (0 : ℝ) < 11 ^ (n - 3) := by positivity
  rw [div_pow, mul_div_assoc', le_div_iff₀ hpos, mul_comm (f n : ℝ)]
  exact H'

/-- `c (r)^(n-3) = (c / r^3) r^n` for `n ≥ 3`. -/
theorem pow_sub_three {r : ℝ} (hr : 0 < r) (c : ℝ) {n : Nat} (hn : 3 ≤ n) :
    c * r ^ (n - 3) = c / r ^ 3 * r ^ n := by
  have e : r ^ n = r ^ (n - 3) * r ^ 3 := by rw [← pow_add, Nat.sub_add_cancel hn]
  have h3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr.ne'
  rw [e, div_mul_eq_mul_div, eq_div_iff h3]
  ring

/-! ### Fekete's lemma for supermultiplicative sequences -/

/-- **Roots of a supermultiplicative sequence with a geometric upper bound converge.** -/
theorem root_limit {g : ℕ → ℕ} (hpos : ∀ n, 1 ≤ g n) (hsup : ∀ m n, g m * g n ≤ g (m + n))
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (hbound : ∀ n, 3 ≤ n → (g n : ℝ) ≤ c * r ^ n) :
    ∃ L, Tendsto (fun n : ℕ => (g n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧ L ≤ r := by
  have gpos : ∀ n, (0 : ℝ) < g n := fun n => by exact_mod_cast hpos n
  set u : ℕ → ℝ := fun n => -Real.log (g n) with hu
  have hsub : Subadditive u := by
    intro m n
    simp only [hu]
    have h1 : Real.log ((g m : ℝ) * g n) ≤ Real.log (g (m + n)) := by
      apply Real.log_le_log (mul_pos (gpos m) (gpos n))
      exact_mod_cast hsup m n
    rw [Real.log_mul (gpos m).ne' (gpos n).ne'] at h1
    linarith
  -- lower bound for `u n / n`
  have hlogle : ∀ n, 3 ≤ n → Real.log (g n) ≤ Real.log c + n * Real.log r := by
    intro n hn
    have := Real.log_le_log (gpos n) (hbound n hn)
    rwa [Real.log_mul hc.ne' (pow_pos hr n).ne', Real.log_pow] at this
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨-(|Real.log c| + |Real.log r| + |u 1| + |u 2|), ?_⟩
    rintro _ ⟨n, rfl⟩
    have a1 := abs_nonneg (Real.log c)
    have a2 := abs_nonneg (Real.log r)
    have a3 := abs_nonneg (u 1)
    have a4 := abs_nonneg (u 2)
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · show _ ≤ u 0 / ((0 : ℕ) : ℝ)
        rw [Nat.cast_zero, div_zero]
        linarith
      · show _ ≤ u 1 / ((1 : ℕ) : ℝ)
        rw [Nat.cast_one, div_one]
        linarith [neg_abs_le (u 1)]
      · show _ ≤ u 2 / ((2 : ℕ) : ℝ)
        push_cast
        linarith [neg_abs_le (u 2)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      rw [le_div_iff₀ hnpos]
      have hun : u n = -Real.log (g n) := rfl
      have p1 : |Real.log c| * 1 ≤ |Real.log c| * n := mul_le_mul_of_nonneg_left hn1 a1
      have p2 : Real.log r * n ≤ |Real.log r| * n :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hnpos.le
      have p3 : 0 ≤ (|u 1| + |u 2|) * n := mul_nonneg (by positivity) hnpos.le
      have p4 := hlogle n hn
      have p5 := le_abs_self (Real.log c)
      rw [hun]
      nlinarith
  have hlim := hsub.tendsto_lim hbdd
  set ℓ := hsub.lim
  -- `log g(n) / n → -ℓ`
  have ha : Tendsto (fun n : ℕ => Real.log (g n) / n) atTop (𝓝 (-ℓ)) := by
    have := hlim.neg
    refine this.congr (fun n => ?_)
    simp only [hu, neg_div, neg_neg]
  refine ⟨Real.exp (-ℓ), ?_, ?_⟩
  · have he := (Real.continuous_exp.tendsto _).comp ha
    refine he.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos (gpos n)]
    congr 1
    ring
  · -- `-ℓ ≤ log r`
    have hb : Tendsto (fun n : ℕ => Real.log c / n + Real.log r) atTop (𝓝 (0 + Real.log r)) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add tendsto_const_nhds
    rw [zero_add] at hb
    have hle : (fun n : ℕ => Real.log (g n) / n) ≤ᶠ[atTop] (fun n : ℕ => Real.log c / n + Real.log r) := by
      filter_upwards [eventually_ge_atTop 3] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have e : Real.log c / n + Real.log r = (Real.log c + n * Real.log r) / n := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right (hlogle n hn) hnpos.le
    have := le_of_tendsto_of_tendsto ha hb hle
    calc Real.exp (-ℓ) ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr this
      _ = r := Real.exp_log hr

/-! ### The limits -/

/-- **`h(n)^(1/n)` converges, to a limit at most `8/3`.** -/
theorem h_root_limit :
    ∃ L, Tendsto (fun n : ℕ => (h n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧ L ≤ 8 / 3 :=
  root_limit CDCert.Supermult.one_le_h CDCert.Supermult.h_supermul (c := 4 / (8 / 3) ^ 3)
    (r := 8 / 3) (by norm_num) (by norm_num) (fun n hn => by
      rw [← pow_sub_three (r := 8 / 3) (by norm_num) 4 hn]; exact h_le_real hn)

/-- **`f(n)^(1/n)` converges, to a limit at most `32/11`.** -/
theorem f_root_limit :
    ∃ L, Tendsto (fun n : ℕ => (f n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧ L ≤ 32 / 11 :=
  root_limit CDCert.Supermult.one_le_f CDCert.Supermult.f_supermul (c := 4 / (32 / 11) ^ 3)
    (r := 32 / 11) (by norm_num) (by norm_num) (fun n hn => by
      rw [← pow_sub_three (r := 32 / 11) (by norm_num) 4 hn]; exact f_le_real hn)

/-! ### The polynomial correction `f(n) = O(n^(-8/11) (32/11)^n)` -/

/-- Bernoulli: `(n + 2)^(8/11) (n + 1) ≤ (n + 1)^(8/11) (n + 1 + 8/11)`. -/
theorem bernoulli_step (n : ℕ) :
    ((n : ℝ) + 2) ^ (8 / 11 : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ (8 / 11 : ℝ) * ((n : ℝ) + 1 + 8 / 11) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : (n : ℝ) + 1 ≠ 0 := hn1.ne'
  have hs : (-1 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hB := rpow_one_add_le_one_add_mul_self hs (p := (8 / 11 : ℝ)) (by norm_num) (by norm_num)
  have e : (n : ℝ) + 2 = ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) := by
    rw [mul_add, mul_one, mul_one_div_cancel hne]; ring
  have hy : (0 : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) := by positivity
  rw [e, Real.mul_rpow hn1.le hy]
  have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hn1 _
  have e2 : (1 + 8 / 11 * (1 / ((n : ℝ) + 1))) * ((n : ℝ) + 1) = (n : ℝ) + 1 + 8 / 11 := by
    rw [add_mul, one_mul, mul_assoc, one_div_mul_cancel hne, mul_one]
  calc ((n : ℝ) + 1) ^ (8 / 11 : ℝ) * (1 + 1 / ((n : ℝ) + 1)) ^ (8 / 11 : ℝ) * ((n : ℝ) + 1)
      = ((n : ℝ) + 1) ^ (8 / 11 : ℝ) * ((1 + 1 / ((n : ℝ) + 1)) ^ (8 / 11 : ℝ) * ((n : ℝ) + 1)) := by
        ring
    _ ≤ ((n : ℝ) + 1) ^ (8 / 11 : ℝ) * ((1 + 8 / 11 * (1 / ((n : ℝ) + 1))) * ((n : ℝ) + 1)) := by
        gcongr
    _ = ((n : ℝ) + 1) ^ (8 / 11 : ℝ) * ((n : ℝ) + 1 + 8 / 11) := by rw [e2]

/-- The constant of the weighted bound. -/
noncomputable def cW : ℝ := 4 * 4 ^ (8 / 11 : ℝ) / (32 / 11) ^ 3

/-- The weighted bound `f(n) (n + 1)^(8/11) ≤ cW (32/11)^n`, `n ≥ 3`. -/
theorem f_weighted {n : ℕ} (hn : 3 ≤ n) :
    (f n : ℝ) * ((n : ℝ) + 1) ^ (8 / 11 : ℝ) ≤ cW * (32 / 11 : ℝ) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  clear hn
  induction k with
  | zero =>
    rw [Nat.add_zero, f_three]
    unfold cW
    rw [div_mul_cancel₀ (4 * 4 ^ (8 / 11 : ℝ)) (show ((32 / 11 : ℝ)) ^ 3 ≠ 0 by norm_num)]
    norm_num
  | succ k ih =>
    rw [show 3 + (k + 1) = (3 + k) + 1 by omega]
    generalize hN : 3 + k = N at ih ⊢
    have hrecN := CDCert.Recurrences.general_recurrence N
    have hrec : (11 * ((N : ℝ) + 1) + 8) * (f (N + 1) : ℝ) ≤ 32 * ((N : ℝ) + 1) * (f N : ℝ) := by
      exact_mod_cast hrecN
    have hB := bernoulli_step N
    have e2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by push_cast; ring
    rw [e2]
    have hF' : (0 : ℝ) ≤ (f (N + 1) : ℝ) := Nat.cast_nonneg _
    have hF : (0 : ℝ) ≤ (f N : ℝ) := Nat.cast_nonneg _
    have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hP : (0 : ℝ) < ((N : ℝ) + 1) ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hx _
    generalize ((N : ℝ) + 1) ^ (8 / 11 : ℝ) = P at hB hP ih
    generalize ((N : ℝ) + 2) ^ (8 / 11 : ℝ) = Q at hB ⊢
    generalize (f (N + 1) : ℝ) = F' at hrec hF' ⊢
    generalize (f N : ℝ) = F at hrec hF ih
    generalize (N : ℝ) = x at hrec hB hx
    have h1 : F' * (Q * (x + 1)) ≤ F' * (P * (x + 1 + 8 / 11)) := mul_le_mul_of_nonneg_left hB hF'
    have h2 : P * ((11 * (x + 1) + 8) * F') ≤ P * (32 * (x + 1) * F) := mul_le_mul_of_nonneg_left hrec hP.le
    have h3 : (x + 1) * (F * P) ≤ (x + 1) * (cW * (32 / 11) ^ N) := mul_le_mul_of_nonneg_left ih hx.le
    have key : F' * Q * (x + 1) ≤ cW * (32 / 11) ^ (N + 1) * (x + 1) := by
      rw [pow_succ]
      linarith
    exact le_of_mul_le_mul_right key hx

/-- **`f(n) = O(n^(-8/11) (32/11)^n)`.** -/
theorem f_isBigO :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(8 / 11 : ℝ)) * (32 / 11 : ℝ) ^ n) := by
  refine Asymptotics.IsBigO.of_bound cW ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hw := f_weighted hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQ : (0 : ℝ) < (n : ℝ) ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hn0 _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) ^ (-(8 / 11 : ℝ)) * (32 / 11 : ℝ) ^ n by positivity),
    Real.rpow_neg hn0.le]
  have hmono : (n : ℝ) ^ (8 / 11 : ℝ) ≤ ((n : ℝ) + 1) ^ (8 / 11 : ℝ) :=
    Real.rpow_le_rpow hn0.le (by linarith) (by norm_num)
  have h1 : (f n : ℝ) * (n : ℝ) ^ (8 / 11 : ℝ) ≤ cW * (32 / 11 : ℝ) ^ n :=
    le_trans (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)) hw
  have h2 : (f n : ℝ) ≤ cW * (32 / 11 : ℝ) ^ n / (n : ℝ) ^ (8 / 11 : ℝ) := (le_div_iff₀ hQ).mpr h1
  calc (f n : ℝ) ≤ cW * (32 / 11 : ℝ) ^ n / (n : ℝ) ^ (8 / 11 : ℝ) := h2
    _ = cW * (((n : ℝ) ^ (8 / 11 : ℝ))⁻¹ * (32 / 11 : ℝ) ^ n) := by
        rw [div_eq_mul_inv]; ring

end CDCert.Asymptotics
