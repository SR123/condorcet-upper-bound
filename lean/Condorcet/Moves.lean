import Condorcet.MaximalPairs

namespace Condorcet

namespace Order
@[simp] theorem insertionSlot_insertAt {α : Type*} [Fintype α]
    (P : Order α) (t : Fin (Fintype.card α+1)) : (P.insertAt t).insertionSlot = t := by
  have H := (P.insertAt t).reconstruct_insertion
  rw [restrict_insertAt] at H
  exact P.insertAt_injective H
end Order

noncomputable def deletedOrder {n : Nat} (x : Fin (n+1)) (r : Order (Fin (n+1))) : Order (Fin n) :=
  Order.restrict (deleteEmbedding x) r

noncomputable def orderSlot {n : Nat} (x : Fin (n+1)) (r : Order (Fin (n+1))) :
    Fin (Fintype.card (Fin n)+1) :=
  (Order.transport (deletionEquiv x).symm r).insertionSlot

@[simp] theorem deletedOrder_labelledInsertion {n : Nat} (x : Fin (n+1))
    (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1)) :
    deletedOrder x (labelledInsertion x P t) = P := by
  exact (restrict_delete_transport x (P.insertAt t)).trans (Order.restrict_insertAt P t)

@[simp] theorem orderSlot_labelledInsertion {n : Nat} (x : Fin (n+1))
    (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1)) :
    orderSlot x (labelledInsertion x P t) = t := by
  simp [orderSlot,labelledInsertion]

theorem labelledInsertion_reconstruct {n : Nat} (x : Fin (n+1)) (r : Order (Fin (n+1))) :
    labelledInsertion x (deletedOrder x r) (orderSlot x r) = r := by
  let r' := Order.transport (deletionEquiv x).symm r
  have hrest : Order.restrict Order.someEmbedding r' = deletedOrder x r := by
    have H := restrict_delete_transport x r'
    simpa [r',deletedOrder] using H.symm
  have H := congrArg (Order.transport (deletionEquiv x)) r'.reconstruct_insertion
  rw [hrest] at H
  simpa [labelledInsertion,r',orderSlot] using H

theorem deletedOrder_slot_injective {n : Nat} (x : Fin (n+1))
    {r s : Order (Fin (n+1))} (hP : deletedOrder x r = deletedOrder x s)
    (ht : orderSlot x r = orderSlot x s) : r = s := by
  rw [← labelledInsertion_reconstruct x r,← labelledInsertion_reconstruct x s,hP,ht]

/-- A lift keeps all other alternatives in order and places x strictly higher. -/
def HasLift {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) (x : Fin (n+1)) : Prop :=
  ∃ s ∈ D, deletedOrder x s = deletedOrder x r ∧ orderSlot x s < orderSlot x r

/-- A drop is the corresponding strictly lower placement. -/
def HasDrop {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) (x : Fin (n+1)) : Prop :=
  ∃ s ∈ D, deletedOrder x s = deletedOrder x r ∧ orderSlot x r < orderSlot x s

def Free {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) (x : Fin (n+1)) : Prop :=
  HasLift D r x ∧ HasDrop D r x

def Frozen {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) (x : Fin (n+1)) : Prop :=
  ¬ HasLift D r x ∧ ¬ HasDrop D r x

theorem hasLift_insertion_iff {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1))
    (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1)) :
    HasLift D (labelledInsertion x P t) x ↔
      ∃ u, u < t ∧ labelledInsertion x P u ∈ D := by
  constructor
  · rintro ⟨s,hs,hP,ht⟩
    simp only [deletedOrder_labelledInsertion,orderSlot_labelledInsertion] at hP ht
    refine ⟨orderSlot x s,ht,?_⟩
    rw [← hP,labelledInsertion_reconstruct]
    exact hs
  · rintro ⟨u,hu,hs⟩
    exact ⟨labelledInsertion x P u,hs,by simp,by simpa using hu⟩

theorem hasDrop_insertion_iff {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1))
    (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n)+1)) :
    HasDrop D (labelledInsertion x P t) x ↔
      ∃ u, t < u ∧ labelledInsertion x P u ∈ D := by
  constructor
  · rintro ⟨s,hs,hP,ht⟩
    simp only [deletedOrder_labelledInsertion,orderSlot_labelledInsertion] at hP ht
    refine ⟨orderSlot x s,ht,?_⟩
    rw [← hP,labelledInsertion_reconstruct]
    exact hs
  · rintro ⟨u,hu,hs⟩
    exact ⟨labelledInsertion x P u,hs,by simp,by simpa using hu⟩

noncomputable def blockedOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    Domain (Fin (n+1)) := by
  classical
  exact D.filter (fun r => ¬ HasLift D r x)

noncomputable def noDropOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    Domain (Fin (n+1)) := by
  classical
  exact D.filter (fun r => ¬ HasDrop D r x)

/-- There is exactly one blocked member in every actual deletion fibre. -/
theorem card_blockedOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    (blockedOrders D x).card = (deleteDomain x D).card := by
  classical
  apply Finset.card_bij (fun r _ => deletedOrder x r)
  · intro r hr
    exact Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩
  · intro r hr s hs hP
    obtain ⟨hr,hrmin⟩ := Finset.mem_filter.mp hr
    obtain ⟨hs,hsmin⟩ := Finset.mem_filter.mp hs
    apply deletedOrder_slot_injective x hP
    apply le_antisymm
    · by_contra H
      exact hrmin ⟨s,hs,hP.symm,lt_of_not_ge H⟩
    · by_contra H
      exact hsmin ⟨r,hr,hP,lt_of_not_ge H⟩
  · intro P hP
    have hn : (insertionSlots (optionDomain x D) P).Nonempty := by
      apply (insertionSlots_nonempty _ _).mpr
      rwa [optionDomain_deletion]
    let t := (insertionSlots (optionDomain x D) P).min' hn
    have ht : t ∈ insertionSlots (optionDomain x D) P := Finset.min'_mem _ hn
    refine ⟨labelledInsertion x P t,?_,deletedOrder_labelledInsertion x P t⟩
    apply Finset.mem_filter.mpr
    refine ⟨(insertionSlots_optionDomain D x P t).mp ht,?_⟩
    rw [hasLift_insertion_iff]
    rintro ⟨u,hu,hum⟩
    have hu' := (insertionSlots_optionDomain D x P u).mpr hum
    have H : t ≤ u := Finset.min'_le _ u hu'
    exact not_lt_of_ge H hu

/-- There is exactly one no-drop member in every actual deletion fibre. -/
theorem card_noDropOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    (noDropOrders D x).card = (deleteDomain x D).card := by
  classical
  apply Finset.card_bij (fun r _ => deletedOrder x r)
  · intro r hr
    exact Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩
  · intro r hr s hs hP
    obtain ⟨hr,hrmax⟩ := Finset.mem_filter.mp hr
    obtain ⟨hs,hsmax⟩ := Finset.mem_filter.mp hs
    apply deletedOrder_slot_injective x hP
    apply le_antisymm
    · by_contra H
      exact hsmax ⟨r,hr,hP,lt_of_not_ge H⟩
    · by_contra H
      exact hrmax ⟨s,hs,hP.symm,lt_of_not_ge H⟩
  · intro P hP
    have hn : (insertionSlots (optionDomain x D) P).Nonempty := by
      apply (insertionSlots_nonempty _ _).mpr
      rwa [optionDomain_deletion]
    let t := (insertionSlots (optionDomain x D) P).max' hn
    have ht : t ∈ insertionSlots (optionDomain x D) P := Finset.max'_mem _ hn
    refine ⟨labelledInsertion x P t,?_,deletedOrder_labelledInsertion x P t⟩
    apply Finset.mem_filter.mpr
    refine ⟨(insertionSlots_optionDomain D x P t).mp ht,?_⟩
    rw [hasDrop_insertion_iff]
    rintro ⟨u,hu,hum⟩
    have hu' := (insertionSlots_optionDomain D x P u).mpr hum
    have H : u ≤ t := Finset.le_max' _ u hu'
    exact not_lt_of_ge H hu

#print axioms labelledInsertion_reconstruct
#print axioms hasLift_insertion_iff
#print axioms hasDrop_insertion_iff
#print axioms card_blockedOrders
#print axioms card_noDropOrders
namespace Order

theorem rank_transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (r : Order α) (b : β) :
    (transport e r).rank b = r.rank (e.symm b) := by
  classical
  unfold rank
  apply Finset.card_bij (fun a _ => e.symm a)
  · intro a ha
    exact (mem_above r (e.symm a) (e.symm b)).mpr ((mem_above (transport e r) a b).mp ha)
  · intro a _ c _ h
    exact e.symm.injective h
  · intro a ha
    refine ⟨e a,?_,e.symm_apply_apply a⟩
    simpa only [mem_above,transport_apply,Equiv.symm_apply_apply] using ha

theorem rank_none_eq_insertionCut {α : Type*} [Fintype α] (r : Order (Option α)) :
    r.rank none = r.insertionCut.card := by
  classical
  have H : r.above none = r.insertionCut.image some := by
    ext a
    cases a with
    | none => simp [mem_above,r.irrefl]
    | some a => simp [mem_above,mem_insertionCut]
  rw [rank,H,Finset.card_image_of_injective _ (fun _ _ h => Option.some.inj h)]

end Order

/-- The slot coordinate is exactly the number of alternatives above x. -/
theorem orderSlot_val_eq_rank {n : Nat} (x : Fin (n+1)) (r : Order (Fin (n+1))) :
    (orderSlot x r).val = r.rank x := by
  change (Order.transport (deletionEquiv x).symm r).insertionCut.card = r.rank x
  rw [← Order.rank_none_eq_insertionCut,Order.rank_transport]
  rfl

theorem hasLift_iff_rank {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1)))
    (x : Fin (n+1)) :
    HasLift D r x ↔ ∃ s ∈ D, deletedOrder x s = deletedOrder x r ∧ s.rank x < r.rank x := by
  simp only [HasLift,Fin.lt_def,orderSlot_val_eq_rank]

theorem hasDrop_iff_rank {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1)))
    (x : Fin (n+1)) :
    HasDrop D r x ↔ ∃ s ∈ D, deletedOrder x s = deletedOrder x r ∧ r.rank x < s.rank x := by
  simp only [HasDrop,Fin.lt_def,orderSlot_val_eq_rank]

noncomputable def freeOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    Domain (Fin (n+1)) := by
  classical
  exact D.filter (fun r => Free D r x)

noncomputable def frozenOrders {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    Domain (Fin (n+1)) := by
  classical
  exact D.filter (fun r => Frozen D r x)

noncomputable def freeCount {n : Nat} (D : Domain (Fin (n+1))) : Nat := by
  classical
  exact ∑ x : Fin (n+1), (freeOrders D x).card

noncomputable def frozenCount {n : Nat} (D : Domain (Fin (n+1))) : Nat := by
  classical
  exact ∑ x : Fin (n+1), (frozenOrders D x).card

theorem first_count_per_alternative {n : Nat} (D : Domain (Fin (n+1))) (x : Fin (n+1)) :
    (blockedOrders D x).card + (noDropOrders D x).card + (freeOrders D x).card =
      D.card + (frozenOrders D x).card := by
  classical
  simp only [blockedOrders,noDropOrders,freeOrders,frozenOrders,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hL : HasLift D r x <;> by_cases hR : HasDrop D r x <;>
    simp [Free,Frozen,hL,hR]

/-- The first exact count in the gap proof, written without Nat subtraction. -/
theorem first_move_count {n : Nat} (D : Domain (Fin (n+1))) :
    2 * deletionSum D + freeCount D = (n+1) * D.card + frozenCount D := by
  classical
  have H := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun x _ => first_count_per_alternative D x)
  simp only [card_blockedOrders,card_noDropOrders,Finset.sum_add_distrib] at H
  simpa [deletionSum,freeCount,frozenCount,Finset.sum_const,two_mul] using H

#print axioms orderSlot_val_eq_rank
#print axioms hasLift_iff_rank
#print axioms first_move_count

end Condorcet
