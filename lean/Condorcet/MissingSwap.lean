import Condorcet.Moves

namespace Condorcet
open CondorcetUpperBounds
namespace Order

theorem consecutive_some_none_slot {α : Type*} [Fintype α] (r : Order (Option α)) (a : α)
    (hr : r (some a) none = true)
    (hcon : ∀ c, ¬(r (some a) c = true ∧ r c none = true)) :
    r.insertionSlot.val = (restrict someEmbedding r).rank a + 1 := by
  classical
  let P := restrict someEmbedding r
  have H : r.insertionCut = insert a (P.above a) := by
    ext c
    simp only [mem_insertionCut,Finset.mem_insert,mem_above]
    constructor
    · intro hc
      by_cases hca : c = a
      · exact Or.inl hca
      · right
        rcases r.total (show (some c : Option α) ≠ some a from fun h => hca (Option.some.inj h)) with h | h
        · exact h
        · exact False.elim (hcon (some c) ⟨h,hc⟩)
    · rintro (rfl | hc)
      · exact hr
      · exact r.trans hc hr
  change r.insertionCut.card = P.rank a + 1
  rw [H,Finset.card_insert_of_notMem]
  · rfl
  · simp [mem_above,P.irrefl]

theorem lift_crosses_some_none {α : Type*} [Fintype α] (r s : Order (Option α)) (a : α)
    (hrest : restrict someEmbedding s = restrict someEmbedding r)
    (hslot : s.insertionSlot < r.insertionSlot) (hr : r (some a) none = true)
    (hcon : ∀ c, ¬(r (some a) c = true ∧ r c none = true)) : s (some a) none = false := by
  have H := consecutive_some_none_slot r a hr hcon
  have hs := s.reconstruct_insertion
  rw [hrest] at hs
  rw [← hs]
  change decide ((restrict someEmbedding r).rank a < s.insertionSlot.val) = false
  simp only [decide_eq_false_iff_not]
  have ht : s.insertionSlot.val < r.insertionSlot.val := hslot
  omega

theorem drop_crosses_none_some {α : Type*} [Fintype α] (r s : Order (Option α)) (a : α)
    (hrest : restrict someEmbedding s = restrict someEmbedding r)
    (hslot : r.insertionSlot < s.insertionSlot) (hr : r none (some a) = true)
    (hcon : ∀ c, ¬(r none c = true ∧ r c (some a) = true)) : s none (some a) = false := by
  have H := congrArg insertionSlot (consecutive_none_insertion r a hr hcon)
  rw [insertionSlot_insertAt] at H
  have hs := s.reconstruct_insertion
  rw [hrest] at hs
  rw [← hs]
  change decide (s.insertionSlot.val ≤ (restrict someEmbedding r).rank a) = false
  simp only [decide_eq_false_iff_not]
  have ht : r.insertionSlot.val < s.insertionSlot.val := hslot
  have Hval := congrArg Fin.val H
  change r.insertionSlot.val = (restrict someEmbedding r).rank a at Hval
  omega

end Order

theorem restrict_optionOrder {n : Nat} (x : Fin (n+1)) (r : Order (Fin (n+1))) :
    Order.restrict Order.someEmbedding (Order.transport (deletionEquiv x).symm r) = deletedOrder x r := by
  have H := restrict_delete_transport x (Order.transport (deletionEquiv x).symm r)
  simpa [deletedOrder] using H.symm

theorem deletedOrder_eq_comparisons {n : Nat} (x : Fin (n+1))
    {r s : Order (Fin (n+1))} (h : deletedOrder x r = deletedOrder x s)
    {a b : Fin (n+1)} (ha : a ≠ x) (hb : b ≠ x) : r a b = s a b := by
  obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq hb
  exact congrArg (fun P : Order (Fin n) => P a b) h

theorem lift_crosses_adjacent {n : Nat} (r s : Order (Fin (n+1))) (p q : Fin (n+1))
    (hpq : p ≠ q) (hrest : deletedOrder q s = deletedOrder q r)
    (hslot : orderSlot q s < orderSlot q r) (hr : r p q = true)
    (hcon : ∀ c, ¬(r p c = true ∧ r c q = true)) : s p q = false := by
  obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hpq
  let e := deletionEquiv q
  let r' := Order.transport e.symm r
  let s' := Order.transport e.symm s
  have h₁ : Order.restrict Order.someEmbedding s' = Order.restrict Order.someEmbedding r' := by
    simpa only [r',s',e,restrict_optionOrder] using hrest
  have h₂ : r' (some a) none = true := by simpa [r',e,ha] using hr
  have h₃ : ∀ c, ¬(r' (some a) c = true ∧ r' c none = true) := by
    intro c
    simpa [r',e,ha] using hcon (e c)
  have H := Order.lift_crosses_some_none r' s' a h₁ hslot h₂ h₃
  simpa [s',e,ha] using H

theorem drop_crosses_adjacent {n : Nat} (r s : Order (Fin (n+1))) (p q : Fin (n+1))
    (hpq : p ≠ q) (hrest : deletedOrder p s = deletedOrder p r)
    (hslot : orderSlot p r < orderSlot p s) (hr : r p q = true)
    (hcon : ∀ c, ¬(r p c = true ∧ r c q = true)) : s p q = false := by
  obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hpq.symm
  let e := deletionEquiv p
  let r' := Order.transport e.symm r
  let s' := Order.transport e.symm s
  have h₁ : Order.restrict Order.someEmbedding s' = Order.restrict Order.someEmbedding r' := by
    simpa only [r',s',e,restrict_optionOrder] using hrest
  have h₂ : r' none (some a) = true := by simpa [r',e,ha] using hr
  have h₃ : ∀ c, ¬(r' none c = true ∧ r' c (some a) = true) := by
    intro c
    simpa [r',e,ha] using hcon (e c)
  have H := Order.drop_crosses_none_some r' s' a h₁ hslot h₂ h₃
  simpa [s',e,ha] using H

/-- The missing-swap lemma via median closure: a lift of the lower alternative
and a drop of the upper one would have the missing swap as their median with r. -/
theorem IsFull.missing_swap {n : Nat} {D : Domain (Fin (n+1))} (hD : IsFull D)
    (r s : Order (Fin (n+1))) (p q : Fin (n+1)) (hpq : p ≠ q)
    (hr : r ∈ D) (hs : s ∉ D) (hrpq : r p q = true) (hspq : s p q = false)
    (hcon : ∀ c, ¬(r p c = true ∧ r c q = true))
    (hoff : ∀ u v, (u,v) ≠ (p,q) → (u,v) ≠ (q,p) → r u v = s u v) :
    ¬ HasLift D r q ∨ ¬ HasDrop D r p := by
  by_contra H
  push_neg at H
  obtain ⟨⟨l,hl,hlP,hlt⟩,⟨d,hd,hdP,hdt⟩⟩ := H
  have hlpq := lift_crosses_adjacent r l p q hpq hlP hlt hrpq hcon
  have hdpq := drop_crosses_adjacent r d p q hpq hdP hdt hrpq hcon
  have hmed : medianOrder hD.isCondorcet r l d hr hl hd = s := by
    ext a b
    simp only [medianOrder_apply]
    by_cases hab : (a,b) = (p,q)
    · have ha : a = p := congrArg Prod.fst hab
      have hb : b = q := congrArg Prod.snd hab
      simpa [ha,hb,hrpq,hlpq,hdpq,hspq,median]
    · by_cases hba : (a,b) = (q,p)
      · have ha : a = q := congrArg Prod.fst hba
        have hb : b = p := congrArg Prod.snd hba
        rw [ha,hb,r.reverse_comparison hpq,l.reverse_comparison hpq,
          d.reverse_comparison hpq,s.reverse_comparison hpq,hrpq,hlpq,hdpq,hspq]
        rfl
      · rw [← hoff a b hab hba]
        by_cases haq : a = q
        · have hap : a ≠ p := by intro H; exact hpq (H.symm.trans haq)
          have hbp : b ≠ p := by intro H; exact hba (Prod.ext haq H)
          have H := deletedOrder_eq_comparisons p hdP hap hbp
          rw [H]
          cases r a b <;> cases l a b <;> rfl
        · by_cases hbq : b = q
          · have hap : a ≠ p := by intro H; exact hab (Prod.ext H hbq)
            have hbp : b ≠ p := by intro H; exact hpq (H.symm.trans hbq)
            have H := deletedOrder_eq_comparisons p hdP hap hbp
            rw [H]
            cases r a b <;> cases l a b <;> rfl
          · have H := deletedOrder_eq_comparisons q hlP haq hbq
            rw [H]
            cases r a b <;> cases d a b <;> rfl
  exact hs (hmed ▸ hD.median_mem r l d hr hl hd)

#print axioms lift_crosses_adjacent
#print axioms drop_crosses_adjacent
#print axioms IsFull.missing_swap
end Condorcet
