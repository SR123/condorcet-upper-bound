/-
CDCert.K6.Base7Sem — what the blocks of a seven-level mask over `base7` are.

For a seven-domain `J` and `m = maskOf base7 J`:
* `blk720 m (720 z)` and `blk720 m (10080 + 720 w)` are the bottom-indexed masks of the six-slices
  `B_z J` and `T_w J`;
* `blk120 m (720 z + 120 x) = m5 (B_x (B_z J))`, `blk120 m (5040 + 720 w + 120 y) = m5 (T_y (T_w J))`,
  `blk120 m (10080 + 720 w + 120 x) = m5 (B_x (T_w J))`, and the top five-slices of `B_z J` sit at
  `10080 + 720 (up z y) + 120 (down (up z y) z)` (`topP_botP`);
* `sliceOK_bots7`, `sliceOK_tops7`: the fourteen descriptors of `bots7`, `tops7` read the slices.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex7
import CDCert.K6.ThetaInv
import CDCert.K6.Seven.Desc

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ### Arithmetic of blocks -/

theorem testBit_add_mul_low {A B L j : Nat} (hA : A < 2 ^ L) (hj : j < L) :
    (A + 2 ^ L * B).testBit j = A.testBit j := by
  have h1 : (A + 2 ^ L * B) % 2 ^ L = A := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]
  have := Nat.testBit_mod_two_pow (A + 2 ^ L * B) L j
  rw [h1, decide_eq_true hj, Bool.true_and] at this
  exact this.symm

theorem shr_mod_low {A B L o w : Nat} (hA : A < 2 ^ L) (h : o + w ≤ L) :
    ((A + 2 ^ L * B) >>> o) % 2 ^ w = (A >>> o) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · rw [testBit_add_mul_low hA (by omega)]
  · simp [hi]

theorem shr_high {A B L : Nat} (hA : A < 2 ^ L) : (A + 2 ^ L * B) >>> L = B := by
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos L), Nat.div_eq_of_lt hA, Nat.zero_add]

theorem shr_mod_nest (A a b W w : Nat) (h : b + w ≤ W) :
    (((A >>> a) % 2 ^ W) >>> b) % 2 ^ w = (A >>> (a + b)) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · rw [decide_eq_true (show b + i < W by omega)]
    simp only [hi, decide_true, Bool.true_and, Nat.add_assoc]
  · simp [hi]

theorem shr_shr (A a b : Nat) : (A >>> a) >>> b = A >>> (a + b) := (Nat.shiftRight_add A a b).symm

theorem blk720_eq' (m o : Nat) : blk720 m o = (m >>> o) % 2 ^ 720 := by
  unfold blk720 m720'
  have : Nat.sub (Nat.shiftLeft 1 720) 1 = 2 ^ 720 - 1 := by
    show (1 <<< 720) - 1 = 2 ^ 720 - 1
    rw [Nat.one_shiftLeft]
  rw [this]
  exact Nat.and_two_pow_sub_one_eq_mod _ 720

/-! ### The copies -/

theorem length_copy1 : copy1.length = 5040 := by decide +kernel
theorem length_copy2 : copy2.length = 5040 := by decide +kernel
theorem length_copy3 : copy3.length = 5040 := by decide +kernel

theorem maskOf_copy1_block (J : List Nat → Bool) {z : Nat} (hz : z < 7) :
    (maskOf copy1 J >>> (720 * z)) % 2 ^ 720 = maskOf (baseB 5) (botP z J) := by
  unfold copy1
  have := maskOf_flatMap_block (fun z => (baseB 5).map (fun M => M.map (up z) ++ [z])) 720 J
    (List.range 7) (fun i _ => by rw [List.length_map, length_baseB5]) z (by simpa using hz)
  rw [this, List.getElem_range, maskOf_map]
  rfl

theorem maskOf_copy2_block (J : List Nat → Bool) {w : Nat} (hw : w < 7) :
    (maskOf copy2 J >>> (720 * w)) % 2 ^ 720 = maskOf (baseT 5) (topP w J) := by
  unfold copy2
  have hl : (baseT 5).length = 720 := by decide
  have := maskOf_flatMap_block (fun w => (baseT 5).map (fun M => w :: M.map (up w))) 720 J
    (List.range 7) (fun i _ => by rw [List.length_map, hl]) w (by simpa using hw)
  rw [this, List.getElem_range, maskOf_map]
  rfl

theorem maskOf_copy3_block (J : List Nat → Bool) {w : Nat} (hw : w < 7) :
    (maskOf copy3 J >>> (720 * w)) % 2 ^ 720 = maskOf (baseB 5) (topP w J) := by
  unfold copy3
  have := maskOf_flatMap_block (fun w => (baseB 5).map (fun M => w :: M.map (up w))) 720 J
    (List.range 7) (fun i _ => by rw [List.length_map, length_baseB5]) w (by simpa using hw)
  rw [this, List.getElem_range, maskOf_map]
  rfl

theorem maskOf_base7 (J : List Nat → Bool) :
    maskOf base7 J = maskOf copy1 J + 2 ^ 5040 * (maskOf copy2 J + 2 ^ 5040 * maskOf copy3 J) := by
  unfold base7
  rw [maskOf_append, maskOf_append, List.length_append, length_copy1, length_copy2]
  rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
  omega

theorem lt_copy (l : List (List Nat)) (hl : l.length = 5040) (J : List Nat → Bool) : maskOf l J < 2 ^ 5040 := by
  rw [← hl]; exact maskOf_lt l J

/-! ### The blocks of `maskOf base7 J` -/

section Blocks
variable (J : List Nat → Bool)

theorem base7_low (o w : Nat) (h : o + w ≤ 5040) :
    (maskOf base7 J >>> o) % 2 ^ w = (maskOf copy1 J >>> o) % 2 ^ w := by
  rw [maskOf_base7]; exact shr_mod_low (lt_copy _ length_copy1 J) h

theorem base7_mid (o w : Nat) (h : o + w ≤ 5040) :
    (maskOf base7 J >>> (5040 + o)) % 2 ^ w = (maskOf copy2 J >>> o) % 2 ^ w := by
  rw [maskOf_base7, ← shr_shr, shr_high (lt_copy _ length_copy1 J)]
  exact shr_mod_low (lt_copy _ length_copy2 J) h

theorem base7_high (o w : Nat) :
    (maskOf base7 J >>> (10080 + o)) % 2 ^ w = (maskOf copy3 J >>> o) % 2 ^ w := by
  rw [maskOf_base7, show (10080 : Nat) + o = 5040 + (5040 + o) by omega, ← shr_shr,
    shr_high (lt_copy _ length_copy1 J), ← shr_shr, shr_high (lt_copy _ length_copy2 J)]

theorem blk720_bot {z : Nat} (hz : z < 7) : blk720 (maskOf base7 J) (720 * z) = maskOf (baseB 5) (botP z J) := by
  rw [blk720_eq', base7_low J _ _ (by omega), maskOf_copy1_block J hz]

theorem blk720_top {w : Nat} (hw : w < 7) :
    blk720 (maskOf base7 J) (10080 + 720 * w) = maskOf (baseB 5) (topP w J) := by
  rw [blk720_eq', base7_high, maskOf_copy3_block J hw]

theorem blk120_bb {z x : Nat} (hz : z < 7) (hx : x < 6) :
    blk120 (maskOf base7 J) (720 * z + 120 * x) = m5 (botP x (botP z J)) := by
  rw [blk120_eq, block, base7_low J _ _ (by omega), ← shr_mod_nest _ _ _ 720 _ (by omega),
    maskOf_copy1_block J hz, block_maskOf_baseB _ hx]
  rfl

theorem blk120_tt {w y : Nat} (hw : w < 7) (hy : y < 6) :
    blk120 (maskOf base7 J) (5040 + 720 * w + 120 * y) = m5 (topP y (topP w J)) := by
  rw [blk120_eq, block, show 5040 + 720 * w + 120 * y = 5040 + (720 * w + 120 * y) by omega,
    base7_mid J _ _ (by omega), ← shr_mod_nest _ _ _ 720 _ (by omega), maskOf_copy2_block J hw,
    block_maskOf_baseT _ hy]
  rfl

theorem blk120_tb {w x : Nat} (hw : w < 7) (hx : x < 6) :
    blk120 (maskOf base7 J) (10080 + 720 * w + 120 * x) = m5 (botP x (topP w J)) := by
  rw [blk120_eq, block, show 10080 + 720 * w + 120 * x = 10080 + (720 * w + 120 * x) by omega,
    base7_high, ← shr_mod_nest _ _ _ 720 _ (by omega), maskOf_copy3_block J hw, block_maskOf_baseB _ hx]
  rfl

theorem blk120_bt {z y : Nat} (hz : z < 7) (hy : y < 6) :
    blk120 (maskOf base7 J) (10080 + 720 * up z y + 120 * down (up z y) z) = m5 (topP y (botP z J)) := by
  have hw : up z y < 7 := up_lt hz hy
  have hx : down (up z y) z < 6 := down_lt hz (Ne.symm (up_ne z y)) hw
  rw [blk120_tb J hw hx, topP_botP]

end Blocks

/-! ### The slice descriptors -/

/-- The descriptor `s` reads the six-domain `H` from the mask `m`. -/
def SliceOK (m : Nat) (s : Slc) (H : List Nat → Bool) : Prop :=
  (∀ f : Nat → Nat, sumOff f m s.1 = ((List.range 6).map (fun x => f (m5 (botP x H)))).sum) ∧
  (∀ f : Nat → Nat, sumOff f m s.2.1 = ((List.range 6).map (fun y => f (m5 (topP y H)))).sum) ∧
  blk720 m s.2.2 = maskOf (baseB 5) H

theorem bots7_get {z : Nat} (hz : z < 7) :
    bots7.getD z ([], [], 0) = ((List.range 6).map (fun x => 720 * z + 120 * x),
      (List.range 6).map (fun y => 10080 + 720 * up z y + 120 * down (up z y) z), 720 * z) := by
  rw [bots7_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz]
  rfl

theorem tops7_get {w : Nat} (hw : w < 7) :
    tops7.getD w ([], [], 0) = ((List.range 6).map (fun x => 10080 + 720 * w + 120 * x),
      (List.range 6).map (fun y => 5040 + 720 * w + 120 * y), 10080 + 720 * w) := by
  rw [tops7_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
  rfl

theorem sliceOK_bots7 (J : List Nat → Bool) {z : Nat} (hz : z < 7) :
    SliceOK (maskOf base7 J) (bots7.getD z ([], [], 0)) (botP z J) := by
  rw [bots7_get hz]
  refine ⟨fun f => ?_, fun f => ?_, blk720_bot J hz⟩
  · rw [sumOff_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp]
    rw [blk120_bb J hz (List.mem_range.mp hx)]
  · rw [sumOff_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y hy
    simp only [Function.comp]
    rw [blk120_bt J hz (List.mem_range.mp hy)]

theorem sliceOK_tops7 (J : List Nat → Bool) {w : Nat} (hw : w < 7) :
    SliceOK (maskOf base7 J) (tops7.getD w ([], [], 0)) (topP w J) := by
  rw [tops7_get hw]
  refine ⟨fun f => ?_, fun f => ?_, blk720_top J hw⟩
  · rw [sumOff_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp]
    rw [blk120_tb J hw (List.mem_range.mp hx)]
  · rw [sumOff_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y hy
    simp only [Function.comp]
    rw [blk120_tt J hw (List.mem_range.mp hy)]

/-- The descriptor of the bottom six-slice `B_z J`. -/
def descB (z : Nat) : Slc := ((List.range 6).map (fun x => 720 * z + 120 * x),
  (List.range 6).map (fun y => 10080 + 720 * up z y + 120 * down (up z y) z), 720 * z)

/-- The descriptor of the top six-slice `T_w J`. -/
def descT (w : Nat) : Slc := ((List.range 6).map (fun x => 10080 + 720 * w + 120 * x),
  (List.range 6).map (fun y => 5040 + 720 * w + 120 * y), 10080 + 720 * w)

theorem bots7_map : bots7 = (List.range 7).map descB := bots7_eq
theorem tops7_map : tops7 = (List.range 7).map descT := tops7_eq

theorem sliceOK_descB (J : List Nat → Bool) {z : Nat} (hz : z < 7) : SliceOK (maskOf base7 J) (descB z) (botP z J) := by
  have := sliceOK_bots7 J hz
  rwa [bots7_get hz] at this

theorem sliceOK_descT (J : List Nat → Bool) {w : Nat} (hw : w < 7) : SliceOK (maskOf base7 J) (descT w) (topP w J) := by
  have := sliceOK_tops7 J hw
  rwa [tops7_get hw] at this

end CDCert.K6
