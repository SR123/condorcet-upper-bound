/-
CDCert.K6.Density — **the density bound at list level**: every `n`-domain `K` (one extreme law per
triple and any fixed pairs) has at most `(5/8) n |K|` enabled adjacent swaps,

  `adj_le : IsDom n K → 8 · A(K) ≤ 5 n |K|`.

The window inequality (`window_bound`, from the finite lemma on all windows of seven consecutive
positions) gives `8D A(K) ≤ 5Dn|K| + B|K|`; applied to the `2^k`-fold ordered self-concatenation
(`dbl`: `|K^{[2^k]}| = |K|^{2^k}`, `A(K^{[2^k]})·|K| = 2^k A(K) |K|^{2^k}`) and divided by `2^k`, the
boundary term vanishes.

With the fibre identity `del + G + A = n|K|` and `G = 0` on `F_n` (Codex's
`deletion_gap_adjacency_identity` and the interval fibres of full extreme-plus-pair domains) this is
Proposition `prop:density`: `del(K) ≥ 3n|K|/8`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Concat

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-- The `2^k`-fold ordered self-concatenation of an `n`-domain. -/
def dbl (n : Nat) (K : List Nat → Bool) : Nat → (List Nat → Bool)
  | 0 => K
  | k + 1 => concat (2 ^ k * n) (dbl n K k) (dbl n K k)

theorem two_pow_succ_mul (k n : Nat) : 2 ^ (k + 1) * n = 2 ^ k * n + 2 ^ k * n := by
  rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.two_mul]

theorem dbl_props {n : Nat} {K : List Nat → Bool} (hK : IsDom n K) (hn : 1 ≤ n) : ∀ k,
    IsDom (2 ^ k * n) (dbl n K k) ∧ card (2 ^ k * n) (dbl n K k) = card n K ^ (2 ^ k) ∧
      adj (2 ^ k * n) (dbl n K k) * card n K = 2 ^ k * adj n K * card n K ^ (2 ^ k)
  | 0 => by
    simp only [Nat.pow_zero, Nat.one_mul, Nat.pow_one]
    exact ⟨hK, rfl, rfl⟩
  | k + 1 => by
    obtain ⟨hd, hc, ha⟩ := dbl_props hK hn k
    have hpos : 1 ≤ 2 ^ k * n := Nat.le_trans hn (Nat.le_mul_of_pos_left n (Nat.pow_pos (by decide)))
    show IsDom (2 ^ (k + 1) * n) (concat (2 ^ k * n) (dbl n K k) (dbl n K k)) ∧
      card (2 ^ (k + 1) * n) (concat (2 ^ k * n) (dbl n K k) (dbl n K k)) = card n K ^ (2 ^ (k + 1)) ∧
      adj (2 ^ (k + 1) * n) (concat (2 ^ k * n) (dbl n K k) (dbl n K k)) * card n K =
        2 ^ (k + 1) * adj n K * card n K ^ (2 ^ (k + 1))
    rw [two_pow_succ_mul k n]
    refine ⟨isDom_concat hd hd, ?_, ?_⟩
    · rw [card_concat, hc, ← Nat.pow_add, ← Nat.two_mul, ← Nat.pow_succ']
    · rw [adj_concat _ _ _ _ hpos hpos, hc]
      have hM : card n K ^ 2 ^ (k + 1) = card n K ^ 2 ^ k * card n K ^ 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
      rw [hM, Nat.pow_succ 2 k]
      generalize card n K ^ 2 ^ k = c at ha ⊢
      generalize adj (2 ^ k * n) (dbl n K k) = a at ha ⊢
      have e1 : (a * c + c * a) * card n K = 2 * (a * card n K) * c := by
        rw [Nat.mul_comm c a, ← Nat.two_mul]; ac_rfl
      rw [e1, ha]
      ac_rfl

theorem adj_zero_of_card {k : Nat} {H : List Nat → Bool} (h : card k H = 0) : adj k H = 0 := by
  unfold adj
  exact nsum_zero _ _ (fun j _ => by have := adjAt_le_card k j H; omega)

/-- **The density bound**: `8 A(K) ≤ 5 n |K|` for every `n`-domain. -/
theorem adj_le {n : Nat} {K : List Nat → Bool} (hK : IsDom n K) : 8 * adj n K ≤ 5 * n * card n K := by
  by_cases hn : n = 0
  · subst hn
    unfold adj
    simp
  have hn1 : 1 ≤ n := by omega
  by_cases hM : card n K = 0
  · rw [adj_zero_of_card hM, hM]; simp
  have hM1 : 1 ≤ card n K := by omega
  apply Classical.byContradiction
  intro hlt
  have hgt : 5 * n * card n K + 1 ≤ 8 * adj n K := by omega
  -- a power of two beyond the boundary constant
  let B : Nat := 10 * 8846117280 + 2 ^ 66
  let k : Nat := B * card n K + 3
  have hk : B * card n K < 2 ^ k := Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega))
  have hk8 : 8 ≤ 2 ^ k := by
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  obtain ⟨hd, hc, ha⟩ := dbl_props hK hn1 k
  have hN : 7 ≤ 2 ^ k * n := Nat.le_trans (by omega) (Nat.mul_le_mul hk8 hn1)
  have hw := window_bound (Or.inl hd) hN
  rw [hc] at hw
  -- multiply by |K| and use `A(K^[2^k]) |K| = 2^k A(K) |K|^{2^k}`
  have hMpos : (0 : Int) < card n K := by exact_mod_cast hM1
  have hw2 := Int.mul_le_mul_of_nonneg_right hw (Int.le_of_lt hMpos)
  have ha' : (adj (2 ^ k * n) (dbl n K k) : Int) * card n K = 2 ^ k * adj n K * ((card n K : Int) ^ 2 ^ k) := by
    exact_mod_cast ha
  have hPpos : (0 : Int) < (card n K : Int) ^ 2 ^ k := Int.pow_pos hMpos
  generalize hP : (card n K : Int) ^ 2 ^ k = P at hw2 ha' hPpos
  have hcast : ((card n K ^ 2 ^ k : Nat) : Int) = P := by rw [← hP]; push_cast; rfl
  rw [hcast] at hw2
  -- hw2 : 8 D a P' ... rewrite into `(...) * P ≤ (...) * P`
  have hl : 8 * 8846117280 * (adj (2 ^ k * n) (dbl n K k) : Int) * card n K = (8 * 8846117280 * 2 ^ k * adj n K) * P := by
    rw [Int.mul_assoc, ha']; ac_rfl
  have hr : (5 * 8846117280 * (((2 ^ k * n : Nat) : Int) * P) + (10 * 8846117280 + 2 ^ 66) * P) * card n K =
      (5 * 8846117280 * 2 ^ k * n * card n K + (10 * 8846117280 + 2 ^ 66) * card n K) * P := by
    have hN : ((2 ^ k * n : Nat) : Int) = (2 : Int) ^ k * n := by rw [Int.natCast_mul, Int.natCast_pow]; rfl
    rw [hN]
    generalize (2 : Int) ^ k = T
    generalize (5 * 8846117280 : Int) = c5
    generalize (10 * 8846117280 + 2 ^ 66 : Int) = cB
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hl, hr] at hw2
  have hfin := Int.le_of_mul_le_mul_right hw2 hPpos
  -- hfin : 8 D 2^k A ≤ 5 D 2^k n M + B M; with 8A ≥ 5nM + 1 this forces 2^k ≤ B M
  have hgt' : (5 * n * card n K : Int) + 1 ≤ 8 * adj n K := by exact_mod_cast hgt
  have hk' : ((B * card n K : Nat) : Int) < 2 ^ k := by exact_mod_cast hk
  have hB : ((B * card n K : Nat) : Int) = (10 * 8846117280 + 2 ^ 66) * card n K := by push_cast; rfl
  rw [hB] at hk'
  have h2k : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  generalize (2 : Int) ^ k = T at hfin hk' h2k
  generalize (adj n K : Int) = A at hfin hgt'
  generalize (card n K : Int) = M at hfin hgt' hk'
  -- 8 D T A ≤ 5 D T n M + B M and 8 A ≥ 5 n M + 1 give D T ≤ B M < T
  have h1 : 8 * 8846117280 * T * A = 8846117280 * T * (8 * A) := by ac_rfl
  have h2 : 5 * 8846117280 * T * (n : Int) * M = 8846117280 * T * (5 * n * M) := by ac_rfl
  rw [h1, h2] at hfin
  have h3 : 8846117280 * T * (5 * n * M + 1) ≤ 8846117280 * T * (8 * A) :=
    Int.mul_le_mul_of_nonneg_left hgt' (Int.le_of_lt (Int.mul_pos (by decide) h2k))
  rw [Int.mul_add, Int.mul_one] at h3
  omega

end CDCert.K6
