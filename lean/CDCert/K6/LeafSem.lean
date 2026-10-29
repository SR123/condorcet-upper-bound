/-
CDCert.K6.LeafSem — what the six-level leaf test `leafOK6` says.

* `blkB_eq`, `blkT_eq`: the memoized block lookups are plain table lookups of
  the 120-bit blocks (with `2^60` for an empty block);
* `ineq6_eq_true_iff`: `ineq6 T m` is the inequality
  `12 * 2^60 ≤ Σ_{x<6} bvB T (block x) + Σ_{y<6} bvT T (block (6+y))`;
* `leafOK6_eq_true_iff`: `leafOK6 T E e` holds iff that inequality holds for the
  decoded state, or its bottom-indexed part is a key of `E`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Sound

namespace CDCert.K6

/-- The 120-bit block of `m` at bit offset `k`. -/
def block (m k : Nat) : Nat := (m >>> k) % 2 ^ 120

/-- Offset bottom contribution of a block value. -/
noncomputable def bvB (T : KTree) (b : Nat) : Nat := if b = 0 then 2 ^ 60 else T.find b % 2 ^ 64

/-- Offset top contribution of a block value. -/
noncomputable def bvT (T : KTree) (b : Nat) : Nat := if b = 0 then 2 ^ 60 else (T.find b >>> 64) % 2 ^ 64

theorem m120_eq : m120 = 2 ^ 120 - 1 := by decide
theorem m64_eq : m64 = 2 ^ 64 - 1 := by decide
theorem off60_eq : off60 = 2 ^ 60 := by decide
theorem off60x12_eq : off60x12 = 12 * 2 ^ 60 := by decide

theorem land_m120 (x : Nat) : Nat.land x m120 = x % 2 ^ 120 := by
  rw [m120_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 120

theorem land_m64 (x : Nat) : Nat.land x m64 = x % 2 ^ 64 := by
  rw [m64_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 64

/-- The encoded block used as memo key. -/
theorem blockEnc_eq (m k : Nat) :
    Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight m k) m120) 64)
      (Nat.mod (Nat.land (Nat.shiftRight m k) m120) hashP) = enc (block m k) := by
  show enc (Nat.land (m >>> k) m120) = enc (block m k)
  rw [land_m120]
  rfl

theorem blkB_eq (T : KTree) (m k : Nat) : blkB T m k = bvB T (block m k) := by
  unfold blkB bvB
  rw [blockEnc_eq]
  by_cases h : block m k = 0
  · rw [if_pos h, h, off60_eq]
    rfl
  · rw [if_neg h]
    have hne : enc (block m k) ≠ 0 := fun h' => h ((enc_eq_zero_iff _).mp h')
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hs]
    show lookB T (Nat.succ s) = _
    unfold lookB
    rw [show Nat.shiftRight (Nat.succ s) 64 = block m k by
      rw [← hs]; exact shiftRight_enc _, land_m64]

theorem blkT_eq (T : KTree) (m k : Nat) : blkT T m k = bvT T (block m k) := by
  unfold blkT bvT
  rw [blockEnc_eq]
  by_cases h : block m k = 0
  · rw [if_pos h, h, off60_eq]
    rfl
  · rw [if_neg h]
    have hne : enc (block m k) ≠ 0 := fun h' => h ((enc_eq_zero_iff _).mp h')
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hs]
    show lookT T (Nat.succ s) = _
    unfold lookT
    rw [show Nat.shiftRight (Nat.succ s) 64 = block m k by
      rw [← hs]; exact shiftRight_enc _, land_m64]
    rfl

/-- **The six-row test, read off.** -/
theorem ineq6_eq_true_iff (T : KTree) (m : Nat) :
    ineq6 T m = true ↔
      12 * 2 ^ 60 ≤
        bvB T (block m 0) + (bvB T (block m 120) + (bvB T (block m 240) +
        (bvB T (block m 360) + (bvB T (block m 480) + (bvB T (block m 600) +
        (bvT T (block m 720) + (bvT T (block m 840) + (bvT T (block m 960) +
        (bvT T (block m 1080) + (bvT T (block m 1200) + bvT T (block m 1320))))))))))) := by
  unfold ineq6
  simp only [blkB_eq, blkT_eq]
  rw [off60x12_eq, Nat.ble_eq]
  rfl

/-- **The six-level leaf test, read off.** -/
theorem leafOK6_eq_true_iff (T E : KTree) (e : Nat) :
    leafOK6 T E e = true ↔ ineq6 T (e >>> 64) = true ∨ E.find ((e >>> 64) % 2 ^ 720) ≠ 0 := by
  have hm720 : Nat.land (Nat.shiftRight e 64) m720 = (e >>> 64) % 2 ^ 720 := by
    show (e >>> 64) &&& (1 <<< 720 - 1) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.and_two_pow_sub_one_eq_mod _ 720
  unfold leafOK6
  rw [hm720]
  have hs : Nat.shiftRight e 64 = e >>> 64 := rfl
  rw [hs]
  cases h : ineq6 T (e >>> 64)
  · show (!(Nat.beq (E.find ((e >>> 64) % 2 ^ 720)) 0)) = true ↔ false = true ∨ _
    simp only [Bool.false_eq_true, false_or]
    cases hb : Nat.beq (E.find ((e >>> 64) % 2 ^ 720)) 0
    · simp only [Bool.not_false, true_iff]
      intro hz
      rw [hz] at hb
      cases hb
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]
      exact Nat.eq_of_beq_eq_true hb
  · show true = true ↔ true = true ∨ _
    simp

end CDCert.K6
