/-
CDCert.K6.Sound — soundness of the kernel-evaluated depth-first check `dfs1`.

* `runE e c`: the encoded state after applying the options of `c` in order;
* `dfs1_sound`: if `dfs1 leafOK gs e = true` then for every choice `c` of one
  option per group, either the final state is `0` (an empty domain) or
  `leafOK` holds at it;
* `shiftRight_stepEnc`, `stepEnc_eq_zero_iff`, `shiftRight_enc`, `enc_eq_zero_iff`:
  for pre-shifted options `o <<< 64` the encoded step is exactly bitwise AND on
  the decoded masks, and it is `0` exactly when the AND is `0`;
* `shiftRight_runE`: decoded final state = decoded start state AND all chosen
  (unshifted) option masks.

The memoization performed by the kernel while evaluating `dfs1` plays no role
here: `dfs1` is an ordinary total function and these are ordinary theorems.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs
import CDCert.Enum

namespace CDCert.K6

open CDCert

/-- Apply the options of `c` in order with `stepEnc`. -/
def runE (e : Nat) : List Nat → Nat
  | [] => e
  | o :: c => runE (stepEnc e o) c

theorem land_eq' (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem lor_eq' (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem mod_eq' (a b : Nat) : Nat.mod a b = a % b := rfl
theorem shiftLeft_eq'' (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem shiftRight_eq'' (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl

theorem stepEnc_eq (e o : Nat) : stepEnc e o = (e &&& o) ||| ((e &&& o) % hashP) := rfl

theorem enc_eq (x : Nat) : enc x = (x <<< 64) ||| (x % hashP) := rfl

theorem stepEnc_zero (o : Nat) : stepEnc 0 o = 0 := by
  rw [stepEnc_eq, Nat.zero_and, Nat.zero_mod, Nat.zero_or]

theorem runE_zero : ∀ (c : List Nat), runE 0 c = 0
  | [] => rfl
  | o :: c => by
    show runE (stepEnc 0 o) c = 0
    rw [stepEnc_zero]
    exact runE_zero c

/-- The option loop of `dfs1` is `true` iff every option passes. -/
theorem optLoop_eq_true (P : Nat → Bool) :
    ∀ (g : List Nat), List.rec (motive := fun _ => Bool) true
        (fun o _ r => Bool.rec (motive := fun _ => Bool) false r (P o)) g = true ↔
      ∀ o, o ∈ g → P o = true
  | [] => by simp
  | o :: g => by
    have ih := optLoop_eq_true P g
    show Bool.rec (motive := fun _ => Bool) false
        (List.rec (motive := fun _ => Bool) true
          (fun o _ r => Bool.rec (motive := fun _ => Bool) false r (P o)) g) (P o) = true ↔ _
    cases hP : P o
    · simp only [List.mem_cons]
      constructor
      · intro h
        cases h
      · intro h
        have := h o (Or.inl rfl)
        rw [hP] at this
        cases this
    · simp only
      rw [ih]
      constructor
      · intro h o' ho'
        rcases List.mem_cons.mp ho' with rfl | ho'
        · exact hP
        · exact h o' ho'
      · intro h o' ho'
        exact h o' (List.mem_cons_of_mem _ ho')

/-- **Soundness of the depth-first check.** -/
theorem dfs1_sound (leafOK : Nat → Bool) :
    ∀ (gs : List (List Nat)) (e : Nat), dfs1 leafOK gs e = true →
      ∀ c, IsChoice c gs → runE e c ≠ 0 → leafOK (runE e c) = true
  | [], e, h, c, hc, _ => by
    rw [isChoice_nil_iff] at hc
    subst hc
    exact h
  | g :: gs, e, h, c, hc, hne => by
    obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
    have hstep := (optLoop_eq_true
      (fun o => Nat.rec (motive := fun _ => Bool) true
        (fun e' _ => dfs1 leafOK gs (Nat.succ e')) (stepEnc e o)) g).mp h o ho
    show leafOK (runE (stepEnc e o) c') = true
    have hne' : runE (stepEnc e o) c' ≠ 0 := hne
    cases hs : stepEnc e o with
    | zero =>
      rw [hs, runE_zero] at hne'
      exact absurd rfl hne'
    | succ e' =>
      rw [hs] at hstep hne'
      exact dfs1_sound leafOK gs (Nat.succ e') hstep c' hc' hne'

/-! ### Encoded states -/

theorem testBit_small {h i : Nat} (hh : h < 2 ^ 64) (hi : 64 ≤ i) : h.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  calc h < 2 ^ 64 := hh
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi

theorem mod_hashP_lt (x : Nat) : x % hashP < 2 ^ 64 := by
  have : x % hashP < hashP := Nat.mod_lt x (by decide)
  have h2 : hashP < 2 ^ 64 := by decide
  omega

theorem shiftRight_lor_small (x h : Nat) (hh : h < 2 ^ 64) :
    (x ||| h) >>> 64 = x >>> 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_or,
    testBit_small hh (by omega), Bool.or_false]

theorem land_shiftLeft_low (e o : Nat) : (e &&& (o <<< 64)) % 2 ^ 64 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < 64
  · rw [Nat.testBit_and, Nat.testBit_shiftLeft]
    have : ¬ (i ≥ 64) := by omega
    simp [hi, this]
  · simp [hi]

theorem shiftRight_land_shiftLeft (e o : Nat) :
    (e &&& (o <<< 64)) >>> 64 = (e >>> 64) &&& o := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft]
  simp

theorem eq_zero_of_shiftRight_eq_zero_of_low {x : Nat} (h1 : x >>> 64 = 0) (h2 : x % 2 ^ 64 = 0) :
    x = 0 := by
  have := Nat.div_add_mod x (2 ^ 64)
  rw [Nat.shiftRight_eq_div_pow] at h1
  rw [h1, h2] at this
  omega

/-- Decoding commutes with the encoded step for pre-shifted options. -/
theorem shiftRight_stepEnc (e o : Nat) :
    stepEnc e (o <<< 64) >>> 64 = (e >>> 64) &&& o := by
  rw [stepEnc_eq, shiftRight_lor_small _ _ (mod_hashP_lt _), shiftRight_land_shiftLeft]

/-- The encoded step is `0` exactly when the decoded AND is `0`. -/
theorem stepEnc_eq_zero_iff (e o : Nat) :
    stepEnc e (o <<< 64) = 0 ↔ (e >>> 64) &&& o = 0 := by
  constructor
  · intro h
    rw [← shiftRight_stepEnc, h]
    rfl
  · intro h
    have hx : e &&& (o <<< 64) = 0 := by
      apply eq_zero_of_shiftRight_eq_zero_of_low
      · rw [shiftRight_land_shiftLeft, h]
      · exact land_shiftLeft_low e o
    rw [stepEnc_eq, hx, Nat.zero_mod, Nat.zero_or]

theorem shiftRight_enc (x : Nat) : enc x >>> 64 = x := by
  rw [enc_eq, shiftRight_lor_small _ _ (mod_hashP_lt _), Nat.shiftLeft_shiftRight]

theorem enc_eq_zero_iff (x : Nat) : enc x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← shiftRight_enc x, h]
    rfl
  · intro h
    subst h
    rfl

/-- AND of a list of masks with a start mask. -/
def andAll (s : Nat) : List Nat → Nat
  | [] => s
  | o :: c => andAll (s &&& o) c

/-- **Decoded final state.** -/
theorem shiftRight_runE : ∀ (e : Nat) (c : List Nat),
    runE e (c.map (· <<< 64)) >>> 64 = andAll (e >>> 64) c
  | e, [] => rfl
  | e, o :: c => by
    show runE (stepEnc e (o <<< 64)) (c.map (· <<< 64)) >>> 64 = andAll ((e >>> 64) &&& o) c
    rw [shiftRight_runE, shiftRight_stepEnc]

theorem andAll_zero : ∀ (c : List Nat), andAll 0 c = 0
  | [] => rfl
  | o :: c => by
    show andAll (0 &&& o) c = 0
    rw [Nat.zero_and]
    exact andAll_zero c

/-- The final encoded state is `0` exactly when the decoded AND is `0`. -/
theorem runE_eq_zero_iff : ∀ (e : Nat), (e = 0 ↔ e >>> 64 = 0) → ∀ (c : List Nat),
    runE e (c.map (· <<< 64)) = 0 ↔ andAll (e >>> 64) c = 0
  | e, he, [] => he
  | e, he, o :: c => by
    show runE (stepEnc e (o <<< 64)) (c.map (· <<< 64)) = 0 ↔ andAll ((e >>> 64) &&& o) c = 0
    have he' : stepEnc e (o <<< 64) = 0 ↔ stepEnc e (o <<< 64) >>> 64 = 0 := by
      rw [stepEnc_eq_zero_iff, shiftRight_stepEnc]
    rw [runE_eq_zero_iff _ he' c, shiftRight_stepEnc]

end CDCert.K6
