/-
CDCert.K6.SevenFinal — **the finite lemma**: every seven-domain `J` satisfies `Λ(J) ≥ η |J|`
(`seven_finite`: `2ηD |J| ≤ 2D Λ(J)`), hence (`finite_lemma`, with the compressed identity `lamD_eq`)

  `(D/5) · cost10(J) ≤ (5/4) D |J| + Σ_z 2D q(B_z J) − Σ_w 2D q(T_w J)`,

i.e. `C(J) ≤ (5/8)|J| + Σ_bottom q(H) − Σ_top q(H)` with `C = cost10/10`, `D = 8846117280`.

* No slice of `J` is exceptional: the R8 receiver argument (`lam_receiver`).
* Some bottom (top) six-slice is a relabelling of an exceptional type `j ≠ 9`: relabel `J` so that
  this slice is the slice at label 6 with exactly the mask of `excRep6[j]` (`relabel_slice`), and
  apply the seed family of `j` on that side (`seven_bot`, `seven_top`: the 26 family theorems of
  `CDCert.K6.Seven.S00`–`S25`); `|J|` and `Λ` are invariant under relabelling.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.S00
import CDCert.K6.Seven.S01
import CDCert.K6.Seven.S02
import CDCert.K6.Seven.S03
import CDCert.K6.Seven.S04
import CDCert.K6.Seven.S05
import CDCert.K6.Seven.S06
import CDCert.K6.Seven.S07
import CDCert.K6.Seven.S08
import CDCert.K6.Seven.S09
import CDCert.K6.Seven.S10
import CDCert.K6.Seven.S11
import CDCert.K6.Seven.S12
import CDCert.K6.Seven.S13
import CDCert.K6.Seven.S14
import CDCert.K6.Seven.S15
import CDCert.K6.Seven.S16
import CDCert.K6.Seven.S17
import CDCert.K6.Seven.S18
import CDCert.K6.Seven.S19
import CDCert.K6.Seven.S20
import CDCert.K6.Seven.S21
import CDCert.K6.Seven.S22
import CDCert.K6.Seven.S23
import CDCert.K6.Seven.S24
import CDCert.K6.Seven.S25
import CDCert.K6.R8

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Masks of six-slices -/

theorem excRep6_lt : ∀ j, j < 14 → excRep6.getD j 0 < 2 ^ 720 := by decide +kernel

/-- A six-slice that agrees with `memB6 m` on the orders has the mask `m`. -/
theorem maskOf_baseB_of_memB6 {p : List Nat → Bool} {m : Nat} (h : ∀ M, M ∈ orders 6 → p M = memB6 m M)
    (hm : m < 2 ^ 720) : maskOf (baseB 5) p = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_maskOf]
  cases hx : (baseB 5)[i]? with
  | none =>
    have hi : 720 ≤ i := by
      have := List.getElem?_eq_none_iff.mp hx
      rw [length_baseB5] at this
      exact this
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))).symm
  | some M =>
    obtain ⟨hi, hM⟩ := List.getElem?_eq_some_iff.mp hx
    show p M = m.testBit i
    rw [h M (mem_baseB (hM ▸ List.getElem_mem hi))]
    unfold memB6
    rw [← hM]
    exact congrArg m.testBit (ix_getElem idxB_baseB' i hi)

/-! ### Moving an exceptional slice to label 6 -/

/-- A slice operation that commutes with relabelling like `botP` and `topP`. -/
def SliceRel (S : Nat → (List Nat → Bool) → List Nat → Bool) : Prop :=
  ∀ {x : Nat} {π : List Nat}, π ∈ orders 7 → x < 7 → ∀ (H : List Nat → Bool) {L : List Nat}, L ∈ orders 6 →
    S x (fun M => H (rlab π M)) L = S (app π x) H (rlab (slicePerm 6 x π) L)

theorem sliceRel_bot : SliceRel botP := fun hπ hx H _ hL => botP_relabel (k := 6) hπ hx H hL
theorem sliceRel_top : SliceRel topP := fun hπ hx H _ hL => topP_relabel (k := 6) hπ hx H hL

theorem relabel_move {S : Nat → (List Nat → Bool) → List Nat → Bool} (hS : SliceRel S)
    {J : List Nat → Bool} (hJ : IsDom 7 J) {z : Nat} (hz : z < 7) {m : Nat} (hiso : IsoM m (S z J)) :
    ∃ J1 : List Nat → Bool, IsDom 7 J1 ∧ card 7 J1 = card 7 J ∧ lamD J1 = lamD J ∧ IsoM m (S 6 J1) := by
  have hπ : swapLast 6 z ∈ orders 7 := swapLast_mem hz
  have h6 : (6 : Nat) < 7 := by decide
  have hρ := slicePerm_mem hπ h6
  refine ⟨fun N => J (rlab (swapLast 6 z) N), isDom_relabel hJ hπ, card_relabel hπ J,
    lamD_relabel (Or.inl hJ) hπ, ?_⟩
  have h1 : ∀ M, M ∈ orders 6 → S 6 (fun N => J (rlab (swapLast 6 z) N)) M =
      (fun M => S z J (rlab (slicePerm 6 6 (swapLast 6 z)) M)) M := by
    intro M hM
    rw [hS hπ h6 J hM, app_swapLast_k hz]
  exact (isoM_congr h1).mpr ((isoM_relabel_iff hρ).mpr hiso)

theorem slicePerm_append {ρ : List Nat} (hρ : ρ ∈ orders 6) {L : List Nat} (hL : L ∈ orders 6) :
    rlab (slicePerm 6 6 (ρ ++ [6])) L = rlab ρ L := by
  have hπ : ρ ++ [6] ∈ orders 7 := append_mem_orders hρ
  rw [rlab_eq_map, rlab_eq_map]
  apply List.map_congr_left
  intro a ha
  have ha' := (mem_of_mem_orders hL a).mp ha
  rw [app_slicePerm hπ (by decide) ha', app_append hρ, app_append hρ, app_of_ge hρ (Nat.le_refl 6)]
  have hu : up 6 a = a := by unfold up; rw [if_pos ha']
  rw [hu]
  have hd : down 6 (app ρ a) = app ρ a := by unfold down; rw [if_pos (app_lt hρ ha')]
  exact hd

theorem relabel_fix {S : Nat → (List Nat → Bool) → List Nat → Bool} (hS : SliceRel S)
    {J1 : List Nat → Bool} (hJ1 : IsDom 7 J1) {m : Nat} (hiso : IsoM m (S 6 J1)) :
    ∃ J' : List Nat → Bool, IsDom 7 J' ∧ card 7 J' = card 7 J1 ∧ lamD J' = lamD J1 ∧
      ∀ M, M ∈ orders 6 → S 6 J' M = memB6 m M := by
  obtain ⟨ρ, hρ, hρm⟩ := isoM_inv hiso
  have hπ : ρ ++ [6] ∈ orders 7 := append_mem_orders hρ
  refine ⟨fun N => J1 (rlab (ρ ++ [6]) N), isDom_relabel hJ1 hπ, card_relabel hπ J1,
    lamD_relabel (Or.inl hJ1) hπ, ?_⟩
  intro M hM
  rw [hS hπ (by decide) J1 hM, app_append hρ, app_of_ge hρ (Nat.le_refl 6), slicePerm_append hρ hM, hρm M hM]

/-- **Relabel an exceptional slice to label 6**, with exactly the mask of its type. -/
theorem relabel_slice {S : Nat → (List Nat → Bool) → List Nat → Bool} (hS : SliceRel S)
    {J : List Nat → Bool} (hJ : IsDom 7 J) {z : Nat} (hz : z < 7) {j : Nat} (hj : j < 14)
    (hiso : IsoM (excRep6.getD j 0) (S z J)) :
    ∃ J' : List Nat → Bool, IsDom 7 J' ∧ card 7 J' = card 7 J ∧ lamD J' = lamD J ∧
      maskOf (baseB 5) (S 6 J') = excRep6.getD j 0 := by
  obtain ⟨J1, hJ1, hc1, hl1, hiso1⟩ := relabel_move hS hJ hz hiso
  obtain ⟨J', hJ', hc', hl', hm'⟩ := relabel_fix hS hJ1 hiso1
  exact ⟨J', hJ', hc'.trans hc1, hl'.trans hl1, maskOf_baseB_of_memB6 hm' (excRep6_lt j hj)⟩

/-! ### The 26 seed families -/

theorem seven_bot {J : List Nat → Bool} (hJ : IsDom 7 J) {j : Nat} (hj : j < 14) (h9 : j ≠ 9)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD j 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  match j, hj, h9, hs with
  | 0, _, _, hs => exact seven_fam_0 hJ hs
  | 1, _, _, hs => exact seven_fam_2 hJ hs
  | 2, _, _, hs => exact seven_fam_4 hJ hs
  | 3, _, _, hs => exact seven_fam_6 hJ hs
  | 4, _, _, hs => exact seven_fam_8 hJ hs
  | 5, _, _, hs => exact seven_fam_10 hJ hs
  | 6, _, _, hs => exact seven_fam_12 hJ hs
  | 7, _, _, hs => exact seven_fam_14 hJ hs
  | 8, _, _, hs => exact seven_fam_16 hJ hs
  | 9, _, h9, _ => exact absurd rfl h9
  | 10, _, _, hs => exact seven_fam_18 hJ hs
  | 11, _, _, hs => exact seven_fam_20 hJ hs
  | 12, _, _, hs => exact seven_fam_22 hJ hs
  | 13, _, _, hs => exact seven_fam_24 hJ hs
  | n + 14, h, _, _ => exact absurd h (by omega)

theorem seven_top {J : List Nat → Bool} (hJ : IsDom 7 J) {j : Nat} (hj : j < 14) (h9 : j ≠ 9)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD j 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  match j, hj, h9, hs with
  | 0, _, _, hs => exact seven_fam_1 hJ hs
  | 1, _, _, hs => exact seven_fam_3 hJ hs
  | 2, _, _, hs => exact seven_fam_5 hJ hs
  | 3, _, _, hs => exact seven_fam_7 hJ hs
  | 4, _, _, hs => exact seven_fam_9 hJ hs
  | 5, _, _, hs => exact seven_fam_11 hJ hs
  | 6, _, _, hs => exact seven_fam_13 hJ hs
  | 7, _, _, hs => exact seven_fam_15 hJ hs
  | 8, _, _, hs => exact seven_fam_17 hJ hs
  | 9, _, h9, _ => exact absurd rfl h9
  | 10, _, _, hs => exact seven_fam_19 hJ hs
  | 11, _, _, hs => exact seven_fam_21 hJ hs
  | 12, _, _, hs => exact seven_fam_23 hJ hs
  | 13, _, _, hs => exact seven_fam_25 hJ hs
  | n + 14, h, _, _ => exact absurd h (by omega)

/-! ### The finite lemma -/

theorem exists_exc {H : List Nat → Bool} (h : ¬ NoExc H) :
    ∃ j, j < 14 ∧ j ≠ 9 ∧ IsoM (excRep6.getD j 0) H := by
  apply Classical.byContradiction
  intro hno
  apply h
  intro j hj h9 hiso
  exact hno ⟨j, hj, h9, hiso⟩

theorem exists_slice {P : Nat → Prop} (h : ¬ ∀ z, z < 7 → P z) : ∃ z, z < 7 ∧ ¬ P z := by
  apply Classical.byContradiction
  intro hno
  apply h
  intro z hz
  apply Classical.byContradiction
  intro hP
  exact hno ⟨z, hz, hP⟩

theorem isDom_of_bot_iso {J : List Nat → Bool} (hJ : DomE 7 J) {z : Nat} (hz : z < 7) {j : Nat} (hj : j < 14)
    (hiso : IsoM (excRep6.getD j 0) (botP z J)) : IsDom 7 J := by
  rcases hJ with hJ | hE
  · exact hJ
  · exact absurd hiso (empty_notIso (fun L hL => hE _ (append_up_mem_orders hz hL)) hj)

theorem isDom_of_top_iso {J : List Nat → Bool} (hJ : DomE 7 J) {w : Nat} (hw : w < 7) {j : Nat} (hj : j < 14)
    (hiso : IsoM (excRep6.getD j 0) (topP w J)) : IsDom 7 J := by
  rcases hJ with hJ | hE
  · exact hJ
  · exact absurd hiso (empty_notIso (fun L hL => hE _ (cons_up_mem_orders hw hL)) hj)

/-- **The finite lemma**: `Λ(J) ≥ η |J|` for every seven-domain (`2ηD|J| ≤ 2DΛ(J)`). -/
theorem seven_finite {J : List Nat → Bool} (hJ : DomE 7 J) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  by_cases hb : ∀ z, z < 7 → NoExc (botP z J)
  · by_cases ht : ∀ w, w < 7 → NoExc (topP w J)
    · exact lam_receiver hJ hb ht
    · obtain ⟨w, hw, hn⟩ := exists_slice ht
      obtain ⟨j, hj, h9, hiso⟩ := exists_exc hn
      obtain ⟨J', hJ', hc, hl, hs⟩ := relabel_slice sliceRel_top (isDom_of_top_iso hJ hw hj hiso) hw hj hiso
      have := seven_top hJ' hj h9 hs
      rw [hc, hl] at this
      exact this
  · obtain ⟨z, hz, hn⟩ := exists_slice hb
    obtain ⟨j, hj, h9, hiso⟩ := exists_exc hn
    obtain ⟨J', hJ', hc, hl, hs⟩ := relabel_slice sliceRel_bot (isDom_of_bot_iso hJ hz hj hiso) hz hj hiso
    have := seven_bot hJ' hj h9 hs
    rw [hc, hl] at this
    exact this

/-- **The finite lemma, scaled** (`D = 8846117280`, `cD5 = D/5`, `11057646600 = (5/4)D`, `qD = 2Dq`):
`(D/5)·cost10(J) ≤ (5/4)D|J| + Σ_z 2D q(B_z J) − Σ_w 2D q(T_w J)`, i.e.
`C(J) ≤ (5/8)|J| + Σ_bottom q − Σ_top q`. -/
theorem finite_lemma {J : List Nat → Bool} (hJ : DomE 7 J) :
    (cD5 : Int) * cost10 J ≤ 11057646600 * card 7 J +
      ((List.range 7).map (fun z => qD (botP z J))).sum - ((List.range 7).map (fun w => qD (topP w J))).sum := by
  have h := seven_finite hJ
  rw [lamD_eq] at h
  have hK : (cK : Int) = 5587021440 := rfl
  have hE : (cE : Int) = 58198140 := rfl
  rw [hK, hE] at h
  omega

end CDCert.K6
