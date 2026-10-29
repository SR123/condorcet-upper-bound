/-
CDCert.K6.GathSem — **the gathers rebuild the three copies**: for every `J`,
`expand1 (maskOf copy1 J) = maskOf base7 J` and `expand3 (maskOf copy3 J) = maskOf base7 J`.

* `testBit_gath3`: bit `k` of a gather is the OR of the source bits that `gatherSpec` lists for `k`
  (when all target and source bits of the rows are below 120, `gatherOK`);
* `mem_copy1`, `mem_copy3`: `copy1` and `copy3` list exactly the orders of `0..6`; `mem_copy2`: the
  entries of `copy2` are orders of `0..6`;
* `testBit_maskOf_idx1`, `testBit_maskOf_idx3`: `idx1`, `idx3` are the positions in `copy1`, `copy3`;
* `gath3_g12` … `gath3_g32`: each gather maps the mask over one copy to the mask over another
  (from the kernel checks `g12_eq` … `g32_eq` of `CDCert.K6.Seven.C7F`–`C7I`);
* `expand1_maskOf`, `expand3_maskOf`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.C7D
import CDCert.K6.Seven.C7E
import CDCert.K6.Seven.C7F
import CDCert.K6.Seven.C7G
import CDCert.K6.Seven.C7H
import CDCert.K6.Seven.C7I
import CDCert.K6.Seven.Data
import CDCert.K6.Base7Sem
import CDCert.K6.Feat
import CDCert.K6.MaskLemmas

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Bits of a gather -/

theorem m120lit_eq : (nat_lit 1329227995784915872903807060280344575 : Nat) = 2 ^ 120 - 1 := by decide

theorem land_shr_one (X k : Nat) : Nat.land (Nat.shiftRight X k) 1 = if X.testBit k then 1 else 0 := by
  rw [land_eq', shiftRight_eq'', Nat.and_one_is_mod]
  have h0 : (X >>> k).testBit 0 = X.testBit k := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  rw [Nat.testBit_zero] at h0
  cases h : X.testBit k
  · rw [h] at h0
    have : ¬ (X >>> k) % 2 = 1 := fun e => by rw [decide_eq_true e] at h0; cases h0
    show (X >>> k) % 2 = 0
    omega
  · rw [h] at h0
    exact of_decide_eq_true h0

theorem testBit_gGroup (o s j : Nat) : ∀ (es : List (Nat × Nat)),
    (gGroup o es s).testBit j = es.any (fun e => decide (e.1 = j) && (decide (e.2 < 120) && s.testBit (o + e.2)))
  | [] => Nat.zero_testBit j
  | e :: es => by
    show (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight s o)
      (nat_lit 1329227995784915872903807060280344575)) e.2) 1) e.1) (gGroup o es s)).testBit j = _
    rw [lor_eq', Nat.testBit_or, testBit_gGroup o s j es, List.any_cons, land_shr_one, m120lit_eq]
    have hX : (Nat.land (Nat.shiftRight s o) (2 ^ 120 - 1)).testBit e.2 =
        (decide (e.2 < 120) && s.testBit (o + e.2)) := by
      rw [land_eq', shiftRight_eq'', Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
        Bool.and_comm]
    rw [hX]
    congr 1
    cases (decide (e.2 < 120) && s.testBit (o + e.2))
    · show (Nat.shiftLeft 0 e.1).testBit j = (decide (e.1 = j) && false)
      rw [Bool.and_false, shiftLeft_eq'', Nat.zero_shiftLeft]
      exact Nat.zero_testBit j
    · show (Nat.shiftLeft 1 e.1).testBit j = (decide (e.1 = j) && true)
      rw [Bool.and_true, testBit_one_shiftLeft]

theorem testBit_gBlk (s j : Nat) : ∀ (blk : List (Nat × List (Nat × Nat))),
    (gBlk blk s).testBit j = blk.any (fun g => (gGroup g.1 g.2 s).testBit j)
  | [] => Nat.zero_testBit j
  | g :: blk => by
    show (Nat.lor (gGroup g.1 g.2 s) (gBlk blk s)).testBit j = _
    rw [lor_eq', Nat.testBit_or, testBit_gBlk s j blk, List.any_cons]

theorem any_filterMap_src (s j o : Nat) : ∀ (es : List (Nat × Nat)),
    (es.filterMap (fun e => if e.1 = j then some (o + e.2) else none)).any s.testBit =
      es.any (fun e => decide (e.1 = j) && s.testBit (o + e.2))
  | [] => rfl
  | e :: es => by
    have ih := any_filterMap_src s j o es
    by_cases h : e.1 = j
    · have e1 : (e :: es).filterMap (fun e => if e.1 = j then some (o + e.2) else none) =
          (o + e.2) :: es.filterMap (fun e => if e.1 = j then some (o + e.2) else none) := by
        rw [List.filterMap_cons, if_pos h]
      rw [e1, List.any_cons, List.any_cons, ih, decide_eq_true h, Bool.true_and]
    · have e1 : (e :: es).filterMap (fun e => if e.1 = j then some (o + e.2) else none) =
          es.filterMap (fun e => if e.1 = j then some (o + e.2) else none) := by
        rw [List.filterMap_cons, if_neg h]
      rw [e1, List.any_cons, ih, decide_eq_false h, Bool.false_and, Bool.false_or]

theorem any_srcOf (s j : Nat) (blk : List (Nat × List (Nat × Nat))) :
    (srcOf blk j).any s.testBit = blk.any (fun g => g.2.any (fun e => decide (e.1 = j) && s.testBit (g.1 + e.2))) := by
  unfold srcOf
  rw [List.any_flatMap]
  exact congrArg (fun f => blk.any f) (funext (fun g => any_filterMap_src s j g.1 g.2))

/-- Rows whose target and source bits are below 120. -/
def RowsOK (blk : List (Nat × List (Nat × Nat))) : Prop :=
  ∀ g, g ∈ blk → ∀ e, e ∈ g.2 → e.1 < 120 ∧ e.2 < 120

theorem rowsOK_of (blk : List (Nat × List (Nat × Nat)))
    (h : blk.all (fun g => g.2.all (fun e => decide (e.1 < 120) && decide (e.2 < 120))) = true) : RowsOK blk := by
  intro g hg e he
  have h1 := List.all_eq_true.mp h g hg
  have h2 := List.all_eq_true.mp h1 e he
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h2
  exact h2

theorem any_congr_mem {α : Type} : ∀ (l : List α) (f g : α → Bool), (∀ a, a ∈ l → f a = g a) → l.any f = l.any g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr_mem l f g (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem testBit_gBlk_eq {blk : List (Nat × List (Nat × Nat))} (hb : RowsOK blk) (s j : Nat) :
    (gBlk blk s).testBit j = (decide (j < 120) && (srcOf blk j).any s.testBit) := by
  rw [testBit_gBlk, any_srcOf]
  by_cases hj : j < 120
  · rw [decide_eq_true hj, Bool.true_and]
    apply any_congr_mem
    intro g hg
    rw [testBit_gGroup]
    apply any_congr_mem
    intro e he
    rw [decide_eq_true (hb g hg e he).2, Bool.true_and]
  · rw [decide_eq_false hj, Bool.false_and, List.any_eq_false]
    intro g hg
    rw [testBit_gGroup, List.any_eq_true]
    rintro ⟨e, he, hc⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at hc
    have := (hb g hg e he).1
    omega

/-- **Bits of a gather.** -/
theorem testBit_gath3 (s : Nat) : ∀ (rows : List (List (Nat × List (Nat × Nat)))), gatherOK rows = true →
    ∀ k, (gath3 rows s).testBit k = ((gatherSpec rows).getD k []).any s.testBit
  | [], _, k => by
    show (0 : Nat).testBit k = (([] : List (List Nat)).getD k []).any s.testBit
    rw [Nat.zero_testBit, List.getD_nil]
    rfl
  | blk :: rows, hok, k => by
    unfold gatherOK at hok
    rw [List.all_cons, Bool.and_eq_true] at hok
    have hb := rowsOK_of blk hok.1
    have ih := testBit_gath3 s rows hok.2
    show (Nat.lor (gBlk blk s) (Nat.shiftLeft (gath3 rows s) 120)).testBit k = _
    have hs : gatherSpec (blk :: rows) = (List.range 120).map (fun j => srcOf blk j) ++ gatherSpec rows := by
      unfold gatherSpec
      rw [List.flatMap_cons]
    rw [hs, lor_eq', shiftLeft_eq'', Nat.testBit_or, Nat.testBit_shiftLeft, testBit_gBlk_eq hb]
    by_cases hk : k < 120
    · rw [decide_eq_true hk, Bool.true_and, decide_eq_false (by omega : ¬ k ≥ 120), Bool.false_and, Bool.or_false,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_map, List.length_range]; exact hk),
        List.getElem?_map, List.getElem?_range hk]
      rfl
    · rw [decide_eq_false hk, Bool.false_and, Bool.false_or, decide_eq_true (by omega : k ≥ 120), Bool.true_and, ih,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [List.length_map, List.length_range]; omega), List.length_map,
        List.length_range]

theorem testBit_gath3_single {rows : List (List (Nat × List (Nat × Nat)))} (hok : gatherOK rows = true)
    {l : List Nat} (hspec : gatherSpec rows = l.map (fun x => [x])) (s k : Nat) :
    (gath3 rows s).testBit k = (match l[k]? with | some i => s.testBit i | none => false) := by
  rw [testBit_gath3 s rows hok k, hspec, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? with
  | none => rfl
  | some i => exact Bool.or_false _

/-! ### The copies list the orders -/

theorem mem_copy1 {M : List Nat} : M ∈ copy1 ↔ M ∈ orders 7 := by
  rw [← mem_byLast (k := 6)]
  unfold copy1 byLast
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨z, hz, L, hL, rfl⟩
    exact ⟨z, hz, L, mem_baseB hL, rfl⟩
  · rintro ⟨z, hz, L, hL, rfl⟩
    exact ⟨z, hz, L, mem_baseB_of_mem_orders hL, rfl⟩

theorem mem_copy3 {M : List Nat} : M ∈ copy3 ↔ M ∈ orders 7 := by
  rw [← mem_byFirst (k := 6)]
  unfold copy3 byFirst
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨w, hw, L, hL, rfl⟩
    exact ⟨w, hw, L, mem_baseB hL, rfl⟩
  · rintro ⟨w, hw, L, hL, rfl⟩
    exact ⟨w, hw, L, mem_baseB_of_mem_orders hL, rfl⟩

theorem mem_copy2 {M : List Nat} (h : M ∈ copy2) : M ∈ orders 7 := by
  rw [← mem_byFirst (k := 6)]
  unfold copy2 at h
  unfold byFirst
  simp only [List.mem_flatMap, List.mem_map] at h ⊢
  obtain ⟨w, hw, L, hL, rfl⟩ := h
  exact ⟨w, hw, L, mem_baseT hL, rfl⟩

theorem idx1_copy1' : copy1.map idx1 = List.range copy1.length := by rw [length_copy1]; exact idx1_copy1
theorem idx3_copy3' : copy3.map idx3 = List.range copy3.length := by rw [length_copy3]; exact idx3_copy3

theorem testBit_maskOf_idx1 (J : List Nat → Bool) {M : List Nat} (hM : M ∈ orders 7) :
    (maskOf copy1 J).testBit (idx1 M) = J M := by
  obtain ⟨h, he⟩ := getElem_ix idx1_copy1' (mem_copy1.mpr hM)
  rw [testBit_maskOf, List.getElem?_eq_getElem h, he]

theorem testBit_maskOf_idx3 (J : List Nat → Bool) {M : List Nat} (hM : M ∈ orders 7) :
    (maskOf copy3 J).testBit (idx3 M) = J M := by
  obtain ⟨h, he⟩ := getElem_ix idx3_copy3' (mem_copy3.mpr hM)
  rw [testBit_maskOf, List.getElem?_eq_getElem h, he]

/-! ### The gathers -/

theorem gath3_g12 (J : List Nat → Bool) : gath3 g12 (maskOf copy1 J) = maskOf copy2 J := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_gath3_single g12_ok g12_eq.1, testBit_maskOf, List.getElem?_map]
  cases h : copy2[k]? with
  | none => rfl
  | some M => exact testBit_maskOf_idx1 J (mem_copy2 (List.mem_of_getElem? h))

theorem gath3_g13 (J : List Nat → Bool) : gath3 g13 (maskOf copy1 J) = maskOf copy3 J := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_gath3_single g13_ok g13_eq.1, testBit_maskOf, List.getElem?_map]
  cases h : copy3[k]? with
  | none => rfl
  | some M => exact testBit_maskOf_idx1 J (mem_copy3.mp (List.mem_of_getElem? h))

theorem gath3_g31 (J : List Nat → Bool) : gath3 g31 (maskOf copy3 J) = maskOf copy1 J := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_gath3_single g31_ok g31_eq.1, testBit_maskOf, List.getElem?_map]
  cases h : copy1[k]? with
  | none => rfl
  | some M => exact testBit_maskOf_idx3 J (mem_copy1.mp (List.mem_of_getElem? h))

theorem gath3_g32 (J : List Nat → Bool) : gath3 g32 (maskOf copy3 J) = maskOf copy2 J := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_gath3_single g32_ok g32_eq.1, testBit_maskOf, List.getElem?_map]
  cases h : copy2[k]? with
  | none => rfl
  | some M => exact testBit_maskOf_idx3 J (mem_copy2 (List.mem_of_getElem? h))

/-! ### The three-copy masks -/

theorem or_shift (a b n : Nat) (ha : a < 2 ^ n) : a ||| (b <<< n) = a + 2 ^ n * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

theorem three_copies (A B C : Nat) (hA : A < 2 ^ 5040) (hB : B < 2 ^ 5040) :
    Nat.lor A (Nat.lor (Nat.shiftLeft B 5040) (Nat.shiftLeft C 10080)) = A + 2 ^ 5040 * (B + 2 ^ 5040 * C) := by
  rw [lor_eq', lor_eq', shiftLeft_eq'', shiftLeft_eq'']
  have e1 : C <<< 10080 = (C <<< 5040) <<< 5040 := by rw [← Nat.shiftLeft_add]
  rw [e1, ← Nat.shiftLeft_or_distrib, or_shift _ _ _ hB, or_shift _ _ _ hA]

/-- **The copy-1 mask determines the three-copy mask.** -/
theorem expand1_maskOf (J : List Nat → Bool) : expand1 (maskOf copy1 J) = maskOf base7 J := by
  unfold expand1
  rw [gath3_g12, gath3_g13, three_copies _ _ _ (lt_copy copy1 length_copy1 J) (lt_copy copy2 length_copy2 J),
    maskOf_base7]

/-- **The copy-3 mask determines the three-copy mask.** -/
theorem expand3_maskOf (J : List Nat → Bool) : expand3 (maskOf copy3 J) = maskOf base7 J := by
  unfold expand3
  rw [gath3_g31, gath3_g32, three_copies _ _ _ (lt_copy copy1 length_copy1 J) (lt_copy copy2 length_copy2 J),
    maskOf_base7]

end CDCert.K6
