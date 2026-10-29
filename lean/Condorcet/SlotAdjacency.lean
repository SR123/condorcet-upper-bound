import Condorcet.ComponentCounting

namespace Condorcet
open CondorcetUpperBounds

namespace Order
variable {α : Type*} [Fintype α]

theorem rank_eq_position_iff (P : Order α) (a : α) (t : Fin (Fintype.card α)) :
    P.rank a = t.val ↔ a = P.atPosition t := by
  constructor
  · intro h
    have H : P.rankIndex a = t := Fin.ext h
    simpa using congrArg P.atPosition H
  · rintro rfl
    exact P.rank_atPosition t

theorem insertAt_step_agree (P : Order α) (t : Fin (Fintype.card α))
    (a b : Option α)
    (h₁ : (a,b) ≠ (none,some (P.atPosition t)))
    (h₂ : (a,b) ≠ (some (P.atPosition t),none)) :
    P.insertAt t.castSucc a b = P.insertAt t.succ a b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hb : b ≠ P.atPosition t := by intro h; exact h₁ (by rw [h])
      have hr : P.rank b ≠ t.val := fun h => hb ((P.rank_eq_position_iff b t).mp h)
      change decide (t.val ≤ P.rank b) = decide (t.val+1 ≤ P.rank b)
      simp only [show (t.val ≤ P.rank b) ↔ (t.val+1 ≤ P.rank b) from by omega]
  | some a =>
    cases b with
    | none =>
      have ha : a ≠ P.atPosition t := by intro h; exact h₂ (by rw [h])
      have hr : P.rank a ≠ t.val := fun h => ha ((P.rank_eq_position_iff a t).mp h)
      change decide (P.rank a < t.val) = decide (P.rank a < t.val+1)
      simp only [show (P.rank a < t.val) ↔ (P.rank a < t.val+1) from by omega]
    | some b => rfl

end Order

/-- Inserting the deleted label at an actual slot, in the original labels. -/
noncomputable def labelledInsertion {n : Nat} (x : Fin (n+1)) (P : Order (Fin n))
    (t : Fin (Fintype.card (Fin n)+1)) : Order (Fin (n+1)) :=
  Order.transport (deletionEquiv x) (P.insertAt t)

theorem labelledInsertion_adjacent {n : Nat} (x : Fin (n+1)) (P : Order (Fin n))
    (t : Fin (Fintype.card (Fin n))) :
    AdjacentSwap (labelledInsertion x P t.castSucc) (labelledInsertion x P t.succ) := by
  let e := deletionEquiv x
  let a : Fin (n+1) := e none
  let b : Fin (n+1) := e (some (P.atPosition t))
  have hne : a ≠ b := fun h => Option.noConfusion (e.injective h)
  have hr : labelledInsertion x P t.castSucc a b = true := by
    change P.insertAt t.castSucc (e.symm (e none)) (e.symm (e (some (P.atPosition t)))) = true
    simp only [Equiv.symm_apply_apply]
    change decide (t.val ≤ P.rank (P.atPosition t)) = true
    simp
  have hs : labelledInsertion x P t.succ a b = false := by
    change P.insertAt t.succ (e.symm (e none)) (e.symm (e (some (P.atPosition t)))) = false
    simp only [Equiv.symm_apply_apply]
    change decide (t.val+1 ≤ P.rank (P.atPosition t)) = false
    simp
  have hoff : ∀ u v, (u,v) ≠ (a,b) → (u,v) ≠ (b,a) →
      labelledInsertion x P t.castSucc u v = labelledInsertion x P t.succ u v := by
    intro u v h₁ h₂
    apply P.insertAt_step_agree t (e.symm u) (e.symm v)
    · intro h
      apply h₁
      have H := congrArg (Prod.map e e) h
      simpa [a,b] using H
    · intro h
      apply h₂
      have H := congrArg (Prod.map e e) h
      simpa [a,b] using H
  exact ⟨a,b,hne,hr,hs,consecutive_of_only_pair_changed hs hoff,hoff⟩

theorem labelledInsertion_connected {n : Nat} {D : Domain (Fin (n+1))}
    (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)))
    (h₁ : labelledInsertion x P t.castSucc ∈ D)
    (h₂ : labelledInsertion x P t.succ ∈ D) :
    Connected D (labelledInsertion x P t.castSucc) (labelledInsertion x P t.succ) := by
  exact Reach.step (Connected.refl h₁) ⟨_,h₂,rfl⟩
    ((oneCoordinate_iff_adjacent _ _).mpr (Or.inr (labelledInsertion_adjacent x P t)))

@[simp] theorem mem_optionDomain_iff {n : Nat} (D : Domain (Fin (n+1)))
    (x : Fin (n+1)) (r : Order (Option (Fin n))) :
    r ∈ optionDomain x D ↔ Order.transport (deletionEquiv x) r ∈ D := by
  classical
  constructor
  · intro hr
    rw [← transport_optionDomain x D]
    exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
  · intro hr
    refine Finset.mem_image.mpr ⟨Order.transport (deletionEquiv x) r,hr,?_⟩
    exact Order.transport_symm_transport _ _

@[simp] theorem insertionSlots_optionDomain {n : Nat} (D : Domain (Fin (n+1)))
    (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1)) :
    t ∈ insertionSlots (optionDomain x D) P ↔ labelledInsertion x P t ∈ D := by
  rw [mem_insertionSlots,mem_optionDomain_iff]
  rfl

#print axioms labelledInsertion_adjacent
#print axioms labelledInsertion_connected
/-- One directed slot edge, with the deleted alternative above its neighbour. -/
noncomputable def slotPair {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1))
    (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n))) : Nat := by
  classical
  exact if labelledInsertion x P t.castSucc ∈ D ∧ labelledInsertion x P t.succ ∈ D then 1 else 0

theorem fibre_adjacentPairs_eq_sum {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1))
    (P : Order (Fin n)) :
    SlotWord.adjacentPairs (insertionWord (optionDomain x D) P) =
      ∑ t : Fin (Fintype.card (Fin n)), slotPair D x P t := by
  classical
  rw [insertionWord,SlotWord.adjacentPairs_ofFn]
  apply Finset.sum_congr rfl
  intro t _
  simp only [insertionSlots_optionDomain]
  by_cases h₁ : labelledInsertion x P t.castSucc ∈ D <;>
    by_cases h₂ : labelledInsertion x P t.succ ∈ D <;>
    simp [slotPair,h₁,h₂]

theorem labelledInsertion_mem_deleted {n : Nat} {D : Domain (Fin (n+1))}
    (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1))
    (hr : labelledInsertion x P t ∈ D) : P ∈ deleteDomain x D := by
  rw [← optionDomain_deletion x D]
  exact (insertionSlots_nonempty _ _).mp ⟨t,(insertionSlots_optionDomain D x P t).mpr hr⟩

theorem slotPair_zero_of_not_deleted {n : Nat} {D : Domain (Fin (n+1))}
    (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)))
    (hP : P ∉ deleteDomain x D) : slotPair D x P t = 0 := by
  classical
  have h : ¬(labelledInsertion x P t.castSucc ∈ D ∧ labelledInsertion x P t.succ ∈ D) :=
    fun h => hP (labelledInsertion_mem_deleted x P t.castSucc h.1)
  simp [slotPair,h]

theorem slotAdjacencyCount_eq_sum {n : Nat} (D : Domain (Fin (n+1))) :
    slotAdjacencyCount D = ∑ x : Fin (n+1), ∑ P : Order (Fin n),
      ∑ t : Fin (Fintype.card (Fin n)), slotPair D x P t := by
  classical
  unfold slotAdjacencyCount
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [fibre_adjacentPairs_eq_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hP
  exact Finset.sum_eq_zero (fun t _ => slotPair_zero_of_not_deleted x P t hP)

theorem sum_components_slotPair {n : Nat} (D : Domain (Fin (n+1)))
    (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n))) :
    ∑ K ∈ components D, slotPair K x P t = slotPair D x P t := by
  classical
  let r := labelledInsertion x P t.castSucc
  let s := labelledInsertion x P t.succ
  by_cases h : r ∈ D ∧ s ∈ D
  · have hc : Connected D r s := labelledInsertion_connected x P t h.1 h.2
    have hrc : r ∈ component D r := (mem_component _ _ _).mpr ⟨h.1,Connected.refl h.1⟩
    have hsc : s ∈ component D r := (mem_component _ _ _).mpr ⟨h.2,hc⟩
    have H : ∀ K ∈ components D, slotPair K x P t = if K = component D r then 1 else 0 := by
      intro K hK
      by_cases heq : K = component D r
      · subst K
        simp only [slotPair]
        change (if r ∈ component D r ∧ s ∈ component D r then 1 else 0) = _
        simp [hrc,hsc]
      · have hrK : r ∉ K := by
          intro hrK
          exact heq ((mem_component_iff_component_eq hK).mp hrK).2.symm
        simp [slotPair,show labelledInsertion x P t.castSucc ∉ K from hrK,heq]
    rw [Finset.sum_congr rfl H]
    have hcomp := component_mem_components h.1
    simp [slotPair,show labelledInsertion x P t.castSucc ∈ D from h.1,
      show labelledInsertion x P t.succ ∈ D from h.2,hcomp]
  · have H : ∀ K ∈ components D, slotPair K x P t = 0 := by
      intro K hK
      have hk : ¬(r ∈ K ∧ s ∈ K) := by
        intro hk
        exact h ⟨((mem_component_iff_component_eq hK).mp hk.1).1,
          ((mem_component_iff_component_eq hK).mp hk.2).1⟩
      exact if_neg hk
    rw [Finset.sum_eq_zero H]
    exact (if_neg h).symm

theorem sum_components_slotAdjacencyCount {n : Nat} (D : Domain (Fin (n+1))) :
    ∑ K ∈ components D, slotAdjacencyCount K = slotAdjacencyCount D := by
  classical
  simp_rw [slotAdjacencyCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact sum_components_slotPair D x P t

/-- Paper Lemma 2.2's exact component deletion identity for actual full domains. -/
theorem IsFull.sum_components_deletionSum {n : Nat} {D : Domain (Fin (n+1))}
    (hD : IsFull D) :
    ∑ K ∈ components D, deletionSum K = deletionSum D + gapCount D := by
  classical
  have H : ∀ K ∈ components D,
      deletionSum K + slotAdjacencyCount K = (n+1) * K.card := by
    intro K hK
    exact (hD.components_inF hK).2.deletion_plus_slotAdjacency
  have hsum := Finset.sum_congr rfl H
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_components_card,
    sum_components_slotAdjacencyCount] at hsum
  have hglobal := global_fibre_run_identity D
  omega

#print axioms slotAdjacencyCount_eq_sum
#print axioms sum_components_slotAdjacencyCount
#print axioms IsFull.sum_components_deletionSum

end Condorcet
