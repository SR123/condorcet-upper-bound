/-
CDCert.K6.MaskSem — what the kernel-evaluated mask functions compute.

* `testBit_liftOf`: bit `i` of `liftOf lifts r` is set iff some set bit `j` of `r`
  has bit `i` set in `lifts[j]`;
* `testBit_relabelI`: bit `i` of `relabelI row d` is set iff some set bit `j` of
  `d` has `row[j] = i`;
* `getL_eq`: `getL rows s = rows.getD s []`;
* `KTree.mem_keys_of_find_ne_zero`: a nonzero lookup is at a stored key;
* `relabelI_maskOf`: on a list of orders `P` whose `lexIdx` values are the
  positions, a relabelling row `P.map (lexIdx ∘ rlab σ)` maps the mask of a set of
  members of `P` to the mask of its image (when `rlab σ` maps `P` into `P`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.LexSem
import CDCert.K6.MaskLemmas

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

/-! ### `liftOf` -/

/-- The loop of `liftOf` from index `q` with accumulator `acc`. -/
noncomputable def liftAux (lifts : List Nat) (r : Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun o _ ih q acc => cond (Nat.testBit r q) (ih (Nat.succ q) (Nat.lor acc o)) (ih (Nat.succ q) acc))
    lifts

theorem liftOf_eq (lifts : List Nat) (r : Nat) : liftOf lifts r = liftAux lifts r 0 0 := rfl

theorem testBit_liftAux (r i : Nat) : ∀ (lifts : List Nat) (q acc : Nat),
    (liftAux lifts r q acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j, ∃ h : j < lifts.length, r.testBit (q + j) = true ∧ lifts[j].testBit i = true
  | [], q, acc => by
    show acc.testBit i = true ↔ _
    simp
  | o :: os, q, acc => by
    show (cond (Nat.testBit r q) (liftAux os r (q + 1) (Nat.lor acc o)) (liftAux os r (q + 1) acc)).testBit i = true ↔ _
    cases hq : Nat.testBit r q
    · rw [cond_false, testBit_liftAux r i os (q + 1) acc]
      constructor
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j + 1, by simp; omega, by rw [show q + (j + 1) = q + 1 + j by omega]; exact h1, h2⟩
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · cases j with
          | zero => rw [Nat.add_zero, hq] at h1; cases h1
          | succ j =>
            exact Or.inr ⟨j, by simp at hj; omega, by rw [show q + 1 + j = q + (j + 1) by omega]; exact h1, h2⟩
    · rw [cond_true, testBit_liftAux r i os (q + 1) (Nat.lor acc o)]
      have hor : (Nat.lor acc o).testBit i = (acc.testBit i || o.testBit i) := Nat.testBit_or acc o i
      rw [hor, Bool.or_eq_true]
      constructor
      · rintro ((h | h) | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨0, by simp, by rw [Nat.add_zero]; exact hq, h⟩
        · exact Or.inr ⟨j + 1, by simp; omega, by rw [show q + (j + 1) = q + 1 + j by omega]; exact h1, h2⟩
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · cases j with
          | zero => exact Or.inl (Or.inr h2)
          | succ j =>
            exact Or.inr ⟨j, by simp at hj; omega, by rw [show q + 1 + j = q + (j + 1) by omega]; exact h1, h2⟩

theorem testBit_liftOf (lifts : List Nat) (r i : Nat) :
    (liftOf lifts r).testBit i = true ↔
      ∃ j, ∃ h : j < lifts.length, r.testBit j = true ∧ lifts[j].testBit i = true := by
  rw [liftOf_eq, testBit_liftAux]
  simp

/-! ### `relabelI` -/

/-- The loop of `relabelI`. -/
noncomputable def relabelAux (row : List Nat) (d : Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun t _ ih q acc => cond (Nat.testBit d q) (ih (Nat.succ q) (Nat.lor acc (Nat.shiftLeft 1 t)))
      (ih (Nat.succ q) acc))
    row

theorem relabelI_eq (row : List Nat) (d : Nat) : relabelI row d = relabelAux row d 0 0 := rfl

theorem testBit_one_shiftLeft (t i : Nat) : (Nat.shiftLeft 1 t).testBit i = decide (t = i) := by
  show (1 <<< t).testBit i = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_relabelAux (d i : Nat) : ∀ (row : List Nat) (q acc : Nat),
    (relabelAux row d q acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j, ∃ h : j < row.length, d.testBit (q + j) = true ∧ row[j] = i
  | [], q, acc => by
    show acc.testBit i = true ↔ _
    simp
  | t :: ts, q, acc => by
    show (cond (Nat.testBit d q) (relabelAux ts d (q + 1) (Nat.lor acc (Nat.shiftLeft 1 t)))
      (relabelAux ts d (q + 1) acc)).testBit i = true ↔ _
    cases hq : Nat.testBit d q
    · rw [cond_false, testBit_relabelAux d i ts (q + 1) acc]
      constructor
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j + 1, by simp; omega, by rw [show q + (j + 1) = q + 1 + j by omega]; exact h1, h2⟩
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · cases j with
          | zero => rw [Nat.add_zero, hq] at h1; cases h1
          | succ j =>
            exact Or.inr ⟨j, by simp at hj; omega, by rw [show q + 1 + j = q + (j + 1) by omega]; exact h1, h2⟩
    · rw [cond_true, testBit_relabelAux d i ts (q + 1) (Nat.lor acc (Nat.shiftLeft 1 t))]
      have hor : (Nat.lor acc (Nat.shiftLeft 1 t)).testBit i =
          (acc.testBit i || (Nat.shiftLeft 1 t).testBit i) := Nat.testBit_or acc _ i
      rw [hor, Bool.or_eq_true, testBit_one_shiftLeft, decide_eq_true_iff]
      constructor
      · rintro ((h | h) | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨0, by simp, by rw [Nat.add_zero]; exact hq, h⟩
        · exact Or.inr ⟨j + 1, by simp; omega, by rw [show q + (j + 1) = q + 1 + j by omega]; exact h1, h2⟩
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · cases j with
          | zero => exact Or.inl (Or.inr h2)
          | succ j =>
            exact Or.inr ⟨j, by simp at hj; omega, by rw [show q + 1 + j = q + (j + 1) by omega]; exact h1, h2⟩

theorem testBit_relabelI (row : List Nat) (d i : Nat) :
    (relabelI row d).testBit i = true ↔
      ∃ j, ∃ h : j < row.length, d.testBit j = true ∧ row[j] = i := by
  rw [relabelI_eq, testBit_relabelAux]
  simp

/-! ### `getL` -/

theorem getL_eq : ∀ (rows : List (List Nat)) (s : Nat), getL rows s = rows.getD s []
  | [], s => by cases s <;> rfl
  | r :: rs, 0 => rfl
  | r :: rs, s + 1 => by
    show getL rs s = _
    rw [getL_eq rs s]
    rfl

/-! ### Keys of trees -/

/-- Keys of a tree, in order. -/
noncomputable def KTree.keys (t : KTree) : List Nat :=
  KTree.rec (motive := fun _ => List Nat) [] (fun _ key _ _ ihl ihr => ihl ++ key :: ihr) t

theorem KTree.mem_keys_of_find_ne_zero : ∀ (t : KTree) (k : Nat), t.find k ≠ 0 → k ∈ t.keys
  | .leaf, k, h => absurd rfl h
  | .node l key v r, k, h => by
    have hfind : (KTree.node l key v r).find k =
        cond (Nat.blt k key) (l.find k) (cond (Nat.blt key k) (r.find k) v) := rfl
    have hkeys : (KTree.node l key v r).keys = l.keys ++ key :: r.keys := rfl
    rw [hkeys]
    rw [hfind] at h
    cases h1 : Nat.blt k key
    · rw [h1, cond_false] at h
      cases h2 : Nat.blt key k
      · rw [h2, cond_false] at h
        have hk1 : ¬ k < key := by
          intro hlt
          have h' : Nat.blt k key = true := by rw [Nat.blt_eq]; exact hlt
          rw [h1] at h'; cases h'
        have hk2 : ¬ key < k := by
          intro hlt
          have h' : Nat.blt key k = true := by rw [Nat.blt_eq]; exact hlt
          rw [h2] at h'; cases h'
        have hk : k = key := by omega
        subst hk
        exact List.mem_append_right _ List.mem_cons_self
      · rw [h2, cond_true] at h
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (KTree.mem_keys_of_find_ne_zero r k h))
    · rw [h1, cond_true] at h
      exact List.mem_append_left _ (KTree.mem_keys_of_find_ne_zero l k h)

/-! ### Relabelling masks of sets of orders -/

/-- **Mask relabelling.** Let `P` be a list of lists on which `lexIdx` is the position,
`σ` a list with `rlab σ` mapping members of `P` to members of `P`, and `D` any list.
Then the row `P.map (fun L => lexIdx (rlab σ L))` maps the mask of `D` over `P` to the
mask of the image of `D ∩ P`. -/
theorem relabelI_maskOf {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    (σ : List Nat) (hσ : ∀ L, L ∈ P → rlab σ L ∈ P) (D : List (List Nat)) :
    relabelI (P.map (fun L => lexIdx (rlab σ L))) (maskOf P (fun L => decide (L ∈ D))) =
      maskOf P (fun M => decide (∃ L, L ∈ D ∧ L ∈ P ∧ rlab σ L = M)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [testBit_relabelI, testBit_maskOf]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rw [List.length_map] at hj
    rw [testBit_maskOf, List.getElem?_eq_getElem hj] at h1
    simp only [decide_eq_true_eq] at h1
    rw [List.getElem_map] at h2
    have hmem : rlab σ P[j] ∈ P := hσ _ (List.getElem_mem hj)
    obtain ⟨hlt, heq⟩ := getElem_lexIdx hP hmem
    have hi : i < P.length := h2 ▸ hlt
    rw [List.getElem?_eq_getElem hi]
    simp only [decide_eq_true_eq]
    refine ⟨P[j], h1, List.getElem_mem hj, ?_⟩
    rw [← heq]
    simp only [h2]
  · intro h
    cases hi : P[i]? with
    | none => rw [hi] at h; cases h
    | some M =>
      rw [hi] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨L, hLD, hLP, hLM⟩ := h
      obtain ⟨hlt, heq⟩ := getElem_lexIdx hP hLP
      have hiP : i < P.length := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨h', _⟩; exact h'
      have hMi : P[i] = M := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨_, h'⟩; exact h'
      refine ⟨lexIdx L, by rw [List.length_map]; exact hlt, ?_, ?_⟩
      · rw [testBit_maskOf, List.getElem?_eq_getElem hlt, heq]
        simp only [decide_eq_true_eq]
        exact hLD
      · rw [List.getElem_map, heq, hLM, ← hMi, lexIdx_getElem hP i hiP]

/-- **Mask relabelling**, predicate form. -/
theorem relabelI_maskOf' {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    (σ : List Nat) (hσ : ∀ L, L ∈ P → rlab σ L ∈ P) (p : List Nat → Bool) :
    relabelI (P.map (fun L => lexIdx (rlab σ L))) (maskOf P p) =
      maskOf P (fun M => decide (∃ L, L ∈ P ∧ p L = true ∧ rlab σ L = M)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [testBit_relabelI, testBit_maskOf]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rw [List.length_map] at hj
    rw [testBit_maskOf, List.getElem?_eq_getElem hj] at h1
    rw [List.getElem_map] at h2
    have hmem : rlab σ P[j] ∈ P := hσ _ (List.getElem_mem hj)
    obtain ⟨hlt, heq⟩ := getElem_lexIdx hP hmem
    have hi : i < P.length := h2 ▸ hlt
    rw [List.getElem?_eq_getElem hi]
    simp only [decide_eq_true_eq]
    refine ⟨P[j], List.getElem_mem hj, h1, ?_⟩
    rw [← heq]
    simp only [h2]
  · intro h
    cases hi : P[i]? with
    | none => rw [hi] at h; cases h
    | some M =>
      rw [hi] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨L, hLP, hLp, hLM⟩ := h
      obtain ⟨hlt, heq⟩ := getElem_lexIdx hP hLP
      have hiP : i < P.length := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨h', _⟩; exact h'
      have hMi : P[i] = M := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨_, h'⟩; exact h'
      refine ⟨lexIdx L, by rw [List.length_map]; exact hlt, ?_, ?_⟩
      · rw [testBit_maskOf, List.getElem?_eq_getElem hlt, heq]
        exact hLp
      · rw [List.getElem_map, heq, hLM, ← hMi, lexIdx_getElem hP i hiP]

/-- Witness leaf test, read off. -/
theorem leafW_sound {rows : List (List Nat)} {nperm nrep : Nat} {hint repT : KTree} {e : Nat}
    (h : leafW rows nperm nrep hint repT e = true) :
    ∃ t k, t < nperm ∧ k < nrep ∧ relabelI (getL rows t) (e >>> 64) = repT.find k := by
  unfold leafW at h
  cases hh : hint.find (Nat.shiftRight e 64) with
  | zero => rw [hh] at h; cases h
  | succ h' =>
    rw [hh] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h' % 256, h' / 256, Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

/-! ### Masks over a base with a general position function -/

theorem getElem_ix {P : List (List Nat)} {ix : List Nat → Nat} (hP : P.map ix = List.range P.length)
    {L : List Nat} (hL : L ∈ P) : ∃ h : ix L < P.length, P[ix L] = L := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have h1 : (P.map ix)[i]'(by rw [List.length_map]; exact hi) = i := by
    rw [List.getElem_of_eq hP (by rw [List.length_map]; exact hi), List.getElem_range]
  rw [List.getElem_map] at h1
  rw [h1]
  exact ⟨hi, rfl⟩

theorem ix_getElem {P : List (List Nat)} {ix : List Nat → Nat} (hP : P.map ix = List.range P.length)
    (i : Nat) (hi : i < P.length) : ix P[i] = i := by
  have h1 : (P.map ix)[i]'(by rw [List.length_map]; exact hi) = i := by
    rw [List.getElem_of_eq hP (by rw [List.length_map]; exact hi), List.getElem_range]
  rw [List.getElem_map] at h1
  exact h1

/-- **Mask relabelling** with a general position function. -/
theorem relabelI_maskOf_ix {P : List (List Nat)} {ix : List Nat → Nat}
    (hP : P.map ix = List.range P.length) (σ : List Nat) (hσ : ∀ L, L ∈ P → rlab σ L ∈ P)
    (p : List Nat → Bool) :
    relabelI (P.map (fun L => ix (rlab σ L))) (maskOf P p) =
      maskOf P (fun M => decide (∃ L, L ∈ P ∧ p L = true ∧ rlab σ L = M)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [testBit_relabelI, testBit_maskOf]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rw [List.length_map] at hj
    rw [testBit_maskOf, List.getElem?_eq_getElem hj] at h1
    rw [List.getElem_map] at h2
    have hmem : rlab σ P[j] ∈ P := hσ _ (List.getElem_mem hj)
    obtain ⟨hlt, heq⟩ := getElem_ix hP hmem
    have hi : i < P.length := h2 ▸ hlt
    rw [List.getElem?_eq_getElem hi]
    simp only [decide_eq_true_eq]
    refine ⟨P[j], List.getElem_mem hj, h1, ?_⟩
    rw [← heq]
    simp only [h2]
  · intro h
    cases hi : P[i]? with
    | none => rw [hi] at h; cases h
    | some M =>
      rw [hi] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨L, hLP, hLp, hLM⟩ := h
      obtain ⟨hlt, heq⟩ := getElem_ix hP hLP
      have hiP : i < P.length := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨h', _⟩; exact h'
      have hMi : P[i] = M := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨_, h'⟩; exact h'
      refine ⟨ix L, by rw [List.length_map]; exact hlt, ?_, ?_⟩
      · rw [testBit_maskOf, List.getElem?_eq_getElem hlt, heq]
        exact hLp
      · rw [List.getElem_map, heq, hLM, ← hMi, ix_getElem hP i hiP]

end CDCert.K6
