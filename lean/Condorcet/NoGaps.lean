import Condorcet.Intervals

namespace Condorcet
namespace SlotWord

def bit (bs : List Bool) (i : Nat) : Bool := bs[i]?.getD false

def Interval (bs : List Bool) : Prop :=
  ∀ i j k : Nat, i ≤ j → j ≤ k → bit bs i = true → bit bs k = true → bit bs j = true

theorem interval_tail {b : Bool} {bs : List Bool} (h : Interval (b :: bs)) : Interval bs := by
  intro i j k hij hjk hi hk
  have H := h (i+1) (j+1) (k+1) (by omega) (by omega)
  simpa [bit] using H hi hk

theorem starts_zero_of_all_false (bs : List Bool) (prev : Bool)
    (h : ∀ i, bit bs i = false) : starts prev bs = 0 := by
  induction bs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
    have hb : b = false := by simpa [bit] using h 0
    subst b
    have ht : ∀ i, bit bs i = false := fun i => by simpa [bit] using h (i+1)
    simpa [starts] using ih false ht

theorem starts_true_zero_of_prefix (bs : List Bool)
    (h : ∀ i j, i ≤ j → bit bs j = true → bit bs i = true) : starts true bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      have hall : ∀ i, bit bs i = false := by
        intro i
        cases hi : bit bs i with
        | false => rfl
        | true =>
          have H := h 0 (i+1) (by omega)
          simp only [bit, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
            Bool.false_eq_true, imp_false, Bool.not_eq_true] at H
          exact hi.symm.trans H
      simpa [starts] using starts_zero_of_all_false bs false hall
    | true =>
      have ht : ∀ i j, i ≤ j → bit bs j = true → bit bs i = true := by
        intro i j hij hj
        have H := h (i+1) (j+1) (by omega)
        simpa [bit] using H hj
      simpa [starts] using ih ht

theorem runs_le_one_of_interval (bs : List Bool) (h : Interval bs) : runs bs ≤ 1 := by
  induction bs with
  | nil => simp [runs, starts]
  | cons b bs ih =>
    cases b with
    | false => simpa [runs, starts] using ih (interval_tail h)
    | true =>
      have hp : ∀ i j, i ≤ j → bit bs j = true → bit bs i = true := by
        intro i j hij hj
        have H := h 0 (i+1) (j+1) (by omega) (by omega) (by simp [bit])
        simpa [bit] using H hj
      have H := starts_true_zero_of_prefix bs hp
      simp [runs, starts, H]

theorem gaps_zero_of_interval (bs : List Bool) (h : Interval bs) : gaps bs = 0 := by
  have H := runs_le_one_of_interval bs h
  exact Nat.sub_eq_zero_of_le H

end SlotWord

theorem insertionWord_bit {α : Type*} [Fintype α] (D : Domain (Option α))
    (P : Order α) (i : Nat) :
    SlotWord.bit (insertionWord D P) i =
      if hi : i < Fintype.card α + 1 then decide (⟨i,hi⟩ ∈ insertionSlots D P) else false := by
  classical
  unfold SlotWord.bit insertionWord
  rw [List.getElem?_ofFn]
  by_cases hi : i < Fintype.card α + 1
  · simp only [dif_pos hi, Option.getD_some]
  · simp only [dif_neg hi, Option.getD_none]

theorem IsExtremeFull.insertionWord_interval {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsExtremeFull D) (x : Fin (n + 1)) (P : Order (Fin n)) :
    SlotWord.Interval (insertionWord (optionDomain x D) P) := by
  classical
  intro i j k hij hjk hi hk
  simp only [insertionWord_bit] at hi hk ⊢
  by_cases hklt : k < Fintype.card (Fin n) + 1
  · have hilt : i < Fintype.card (Fin n) + 1 := by omega
    have hjlt : j < Fintype.card (Fin n) + 1 := by omega
    simp only [dif_pos hilt, decide_eq_true_eq] at hi
    simp only [dif_pos hklt, decide_eq_true_eq] at hk
    simp only [dif_pos hjlt, decide_eq_true_eq]
    exact hD.insertionSlots_interval x P (show (⟨i,hilt⟩ : Fin _) ≤ ⟨j,hjlt⟩ from hij)
      (show (⟨j,hjlt⟩ : Fin _) ≤ ⟨k,hklt⟩ from hjk) hi hk
  · simp only [dif_neg hklt, Bool.false_eq_true] at hk

/-- Full extreme-plus-pair domains have no insertion-fibre gaps. -/
theorem IsExtremeFull.gapCount_zero {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsExtremeFull D) : gapCount D = 0 := by
  classical
  unfold gapCount
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro P _
  exact SlotWord.gaps_zero_of_interval _ (hD.insertionWord_interval x P)

theorem IsExtremeFull.deletion_plus_slotAdjacency {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsExtremeFull D) : deletionSum D + slotAdjacencyCount D = (n+1) * D.card := by
  simpa [hD.gapCount_zero] using global_fibre_run_identity D

theorem maximum_peakPit_gapCount_zero {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsPeakPit D) (hcard : D.card = h (n + 1)) : gapCount D = 0 :=
  (maximum_peakPit_fullClass hD hcard).gapCount_zero

#print axioms maximum_peakPit_gapCount_zero
#print axioms SlotWord.runs_le_one_of_interval
#print axioms IsExtremeFull.gapCount_zero
#print axioms IsExtremeFull.deletion_plus_slotAdjacency
end Condorcet
