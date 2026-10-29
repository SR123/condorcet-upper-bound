/-
CDCert.K6.MaskLemmas — bit-level facts about `maskOf` used to read off the
six-level kernel check.

* `testBit_maskOf`: bit `i` of `maskOf base p` is `p` of the `i`-th entry;
* `maskOf_and`, `maskOf_or`: bitwise operations on masks are conjunction and
  disjunction of predicates;
* `maskOf_append`, `maskOf_append_mod`, `maskOf_append_div`: masks over
  concatenated bases;
* `maskOf_map`: masks over mapped bases;
* `maskOf_flatMap_block`: the `x`-th block of a mask over a base made of
  blocks of equal length `w`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Bitset

namespace CDCert.K6

open CDCert CDCert.Bits

variable {α ι : Type}

theorem testBit_maskOf : ∀ (base : List α) (p : α → Bool) (i : Nat),
    (maskOf base p).testBit i = (match base[i]? with | some x => p x | none => false)
  | [], p, i => by simp [maskOf]
  | x :: xs, p, 0 => by
    simp only [maskOf, Nat.testBit_zero, List.getElem?_cons_zero]
    cases p x <;> simp <;> omega
  | x :: xs, p, i + 1 => by
    rw [Nat.testBit_add_one, maskOf_cons_div_two, testBit_maskOf xs p i]
    simp

theorem maskOf_and (base : List α) (p q : α → Bool) :
    (maskOf base p &&& maskOf base q) = maskOf base (fun x => p x && q x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_maskOf, testBit_maskOf, testBit_maskOf]
  cases base[i]? <;> simp

theorem maskOf_or (base : List α) (p q : α → Bool) :
    (maskOf base p ||| maskOf base q) = maskOf base (fun x => p x || q x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_maskOf, testBit_maskOf, testBit_maskOf]
  cases base[i]? <;> simp

theorem maskOf_map (l : List ι) (g : ι → α) (p : α → Bool) :
    maskOf (l.map g) p = maskOf l (fun i => p (g i)) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, maskOf, ih]

theorem maskOf_append (b₁ b₂ : List α) (p : α → Bool) :
    maskOf (b₁ ++ b₂) p = maskOf b₁ p + 2 ^ b₁.length * maskOf b₂ p := by
  induction b₁ with
  | nil => simp [maskOf]
  | cons x xs ih =>
    simp only [List.cons_append, maskOf, ih, List.length_cons, Nat.pow_succ]
    have : 2 ^ xs.length * 2 * maskOf b₂ p = 2 * (2 ^ xs.length * maskOf b₂ p) := by
      rw [Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc]
    rw [this]
    generalize 2 ^ xs.length * maskOf b₂ p = X
    omega

theorem maskOf_append_mod (b₁ b₂ : List α) (p : α → Bool) :
    maskOf (b₁ ++ b₂) p % 2 ^ b₁.length = maskOf b₁ p := by
  rw [maskOf_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (maskOf_lt b₁ p)]

theorem maskOf_append_div (b₁ b₂ : List α) (p : α → Bool) :
    maskOf (b₁ ++ b₂) p / 2 ^ b₁.length = maskOf b₂ p := by
  rw [maskOf_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (maskOf_lt b₁ p), Nat.zero_add]

/-- **Blocks of a mask.** For a base made of blocks of length `w`, the `x`-th
`w`-bit block of the mask is the mask over the `x`-th block. -/
theorem maskOf_flatMap_block (f : ι → List α) (w : Nat) (p : α → Bool) :
    ∀ (l : List ι), (∀ i, i ∈ l → (f i).length = w) →
      ∀ (x : Nat) (hx : x < l.length),
        (maskOf (l.flatMap f) p >>> (w * x)) % 2 ^ w = maskOf (f (l[x]'hx)) p
  | [], _, x, hx => absurd hx (Nat.not_lt_zero _)
  | i :: l, hw, 0, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.shiftRight_zero, ← hw i List.mem_cons_self,
      maskOf_append_mod]
    rfl
  | i :: l, hw, x + 1, hx => by
    rw [List.flatMap_cons, Nat.shiftRight_eq_div_pow]
    have hwi : (f i).length = w := hw i List.mem_cons_self
    have hsplit : 2 ^ (w * (x + 1)) = 2 ^ w * 2 ^ (w * x) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hsplit, ← Nat.div_div_eq_div_mul, ← hwi, maskOf_append_div, hwi,
      ← Nat.shiftRight_eq_div_pow]
    exact maskOf_flatMap_block f w p l (fun j hj => hw j (List.mem_cons_of_mem _ hj)) x
      (by simpa using hx)

end CDCert.K6
