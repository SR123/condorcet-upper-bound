/-
CDCert.K6.TabSemA — relabelling invariance of the five-table, from the kernel
check `T2` (as a hypothesis here; instantiated in `CDCert.K6.TabSem`) and the
five-level coverage.

* `allNat_iff`: `allNat p l = true ↔ ∀ x ∈ l, p x = true`;
* `invarOK_sound`: what `invarOK` checks;
* `find_relabel_rep`: under `T2`, relabelling a representative's domain does not
  change its table value;
* `tabInv_of_T2`: `TabInv` (`CDCert.K6.SumInv`) from `T2`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.SumInv
import CDCert.K6.FiveSem
import CDCert.K6.DefsT

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000

theorem allNat_iff (p : Nat → Bool) : ∀ (l : List Nat), allNat p l = true ↔ ∀ x, x ∈ l → p x = true
  | [] => by simp [allNat]
  | x :: xs => by
    show (Bool.and (p x) (allNat p xs)) = true ↔ _
    rw [Bool.and_eq_true, allNat_iff p xs]
    simp

theorem invarOK_sound {T : KTree} {rows : List (List Nat)} {r : Nat} (h : invarOK T rows r = true) :
    T.find r ≠ 0 ∧ ∀ row, row ∈ rows → T.find (relabelI row r) = T.find r := by
  unfold invarOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro h0
    revert h1
    rw [h0]
    decide
  clear h1
  induction rows with
  | nil => intro row hr; cases hr
  | cons row rs ih =>
    intro row' hr'
    have h2' : Bool.and (Nat.beq (T.find (relabelI row r)) (T.find r))
        (List.rec (motive := fun _ => Bool) true
          (fun row _ ih => Bool.and (Nat.beq (T.find (relabelI row r)) (T.find r)) ih) rs) = true := h2
    rw [Bool.and_eq_true] at h2'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact Nat.eq_of_beq_eq_true h2'.1
    · exact ih h2'.2 row' hr'

theorem lt_pow_of_mem_reps5 {r : Nat} (hr : r ∈ reps5) : r < 2 ^ (lexOrders 5).length := by
  have h : reps5.all (fun r => decide (r < 2 ^ 120)) = true := by decide +kernel
  rw [length_lexOrders5']
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- **Relabelling a representative.** Under `T2`, for every permutation `τ` of `0..4`,
the domain `L ↦ memM r (rlab τ L)` has the table value of `r`. -/
theorem find_relabel_rep (hT2 : ∀ r, r ∈ reps5 → invarOK table5 rows5 r = true) {r : Nat}
    (hr : r ∈ reps5) {τ : List Nat} (hτ : τ ∈ orders 5) :
    table5.find (m5 (fun L => memM r (rlab τ L))) = table5.find r := by
  have hinv := pinv_mem_orders hτ
  obtain ⟨hlt, heq⟩ := getElem_lexIdx lexIdx_lexOrders5'' (mem_lexOrders.mpr hinv)
  have hs : lexIdx (pinv 5 τ) < 120 := by rw [← length_lexOrders5']; exact hlt
  obtain ⟨σ, hσ, hrow⟩ := getL_rows5 hs
  -- the row is the one of `pinv τ`
  have hσeq : σ = pinv 5 τ := by
    have h1 : getL rows5 (lexIdx (pinv 5 τ)) = (lexOrders 5).map (fun L => lexIdx (rlab (pinv 5 τ) L)) := by
      rw [getL_eq, rows5_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, heq]
      rfl
    rw [hrow] at h1
    -- compare the images of the identity order
    have hid : [0, 1, 2, 3, 4] ∈ lexOrders 5 := by decide +kernel
    have h2 := (List.map_inj_left.mp h1) _ hid
    have hσ' := rlab_mem_orders hσ (mem_lexOrders.mp hid)
    have hτ' := rlab_mem_orders hinv (mem_lexOrders.mp hid)
    obtain ⟨_, e1⟩ := getElem_lexIdx lexIdx_lexOrders5'' (mem_lexOrders.mpr hσ')
    obtain ⟨_, e2⟩ := getElem_lexIdx lexIdx_lexOrders5'' (mem_lexOrders.mpr hτ')
    have h3 : rlab σ [0, 1, 2, 3, 4] = rlab (pinv 5 τ) [0, 1, 2, 3, 4] := by
      rw [← e1, ← e2]; simp only [h2]
    have e3 : ∀ π : List Nat, π ∈ orders 5 → rlab π [0, 1, 2, 3, 4] = π := by
      intro π hπ
      have hl := length_of_mem_orders hπ
      rw [rlab_eq_map]
      apply List.ext_getElem
      · simp [hl]
      · intro j h1 h2
        simp only [List.length_map, List.length_cons, List.length_nil] at h1
        rw [List.getElem_map]
        have : [0, 1, 2, 3, 4][j]'(by simp; omega) = j := by
          match j, h1 with
          | 0, _ => rfl
          | 1, _ => rfl
          | 2, _ => rfl
          | 3, _ => rfl
          | 4, _ => rfl
        rw [this, app_of_lt hπ (by omega)]
    rw [e3 σ hσ, e3 _ hinv] at h3
    exact h3
  subst hσeq
  have hT := (invarOK_sound (hT2 r hr)).2 (getL rows5 (lexIdx (pinv 5 τ)))
    (by
      rw [getL_eq, List.getD_eq_getElem?_getD]
      have hl : lexIdx (pinv 5 τ) < rows5.length := by rw [rows5_eq, List.length_map]; exact hlt
      rw [List.getElem?_eq_getElem hl]
      exact List.getElem_mem hl)
  rw [hrow] at hT
  rw [← hT]
  have hmr : relabelI ((lexOrders 5).map (fun L => lexIdx (rlab (pinv 5 τ) L))) r =
      relabelI ((lexOrders 5).map (fun L => lexIdx (rlab (pinv 5 τ) L))) (maskOf (lexOrders 5) (memM r)) := by
    rw [maskOf_memM lexIdx_lexOrders5'' (lt_pow_of_mem_reps5 hr)]
  rw [hmr, relabelI_maskOf' lexIdx_lexOrders5'' _ (fun L hL => mem_lexOrders.mpr
      (rlab_mem_orders hinv (mem_lexOrders.mp hL)))]
  congr 1
  apply m5_congr
  intro M hM
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro h
    refine ⟨rlab τ M, mem_lexOrders.mpr (rlab_mem_orders hτ hM), h, ?_⟩
    exact rlab_pinv_rlab hτ M
  · rintro ⟨L, hL, hrL, hLM⟩
    rw [← hLM, rlab_rlab_pinv hτ]
    exact hrL

/-- **`TabInv` from the kernel check `T2`.** -/
theorem tabInv_of_T2 (hT2 : ∀ r, r ∈ reps5 → invarOK table5 rows5 r = true) : TabInv := by
  intro p hp σ hσ
  by_cases he : IsEmptyOn 5 p
  · have h1 : m5 p = 0 := (m5_eq_zero_iff p).mpr he
    have h2 : m5 (fun L => p (rlab σ L)) = 0 := (m5_eq_zero_iff _).mpr ((isEmptyOn_relabel_iff hσ).mpr he)
    rw [h1, h2]
  · -- a nonempty domain is a relabelled representative
    have : ∃ L0, L0 ∈ orders 5 ∧ p L0 = true := by
      apply Classical.byContradiction
      intro hno
      apply he
      intro L hL
      cases h : p L
      · rfl
      · exact absurd ⟨L, hL, h⟩ hno
    obtain ⟨L0, hL0, hp0⟩ := this
    obtain ⟨c, hc, hpc⟩ := hp
    obtain ⟨ρ, hρ, k, hk, hiso⟩ := five_cover hc hL0 (by rw [← hpc L0 hL0]; exact hp0)
    have hR : rep5T.find k ∈ reps5 := by
      have h := rep5T_eq
      have hl : k < ((List.range 1160).map rep5T.find).length := by simp; exact hk
      have := List.getElem_mem hl
      rw [List.getElem_map, List.getElem_range, h] at this
      exact this
    have e1 : m5 p = m5 (fun L => memM (rep5T.find k) (rlab ρ L)) :=
      m5_congr (fun L hL => (hpc L hL).trans (hiso L hL))
    have e2 : m5 (fun L => p (rlab σ L)) = m5 (fun L => memM (rep5T.find k) (rlab (σ.map (app ρ)) L)) :=
      m5_congr (fun L hL => by
        rw [hpc _ (rlab_mem_orders hσ hL), hiso _ (rlab_mem_orders hσ hL), rlab_comp hρ hσ])
    rw [e1, e2, find_relabel_rep hT2 hR hρ, find_relabel_rep hT2 hR (comp_mem_orders hρ hσ)]

end CDCert.K6
