import Condorcet.SlotAdjacency

namespace Condorcet
namespace Order
variable {α : Type*} [Fintype α]

/-- Converse local geometry: if the distinguished alternative swaps with its
immediate successor, the two orders occupy exactly two consecutive slots. -/
theorem swap_none_slots (r s : Order (Option α)) (a : α)
    (hr : r none (some a) = true) (hs : s none (some a) = false)
    (hcon : ∀ c, ¬(r none c = true ∧ r c (some a) = true))
    (hoff : ∀ u v, (u,v) ≠ (none,some a) → (u,v) ≠ (some a,none) → r u v = s u v) :
    ∃ (P : Order α) (t : Fin (Fintype.card α)),
      r = P.insertAt t.castSucc ∧ s = P.insertAt t.succ := by
  classical
  let P := restrict someEmbedding r
  have hrest : restrict someEmbedding s = P := by
    ext u v
    exact (hoff (some u) (some v) (by simp) (by simp)).symm
  have hcut : r.insertionCut = P.above a := by
    ext c
    simp only [mem_insertionCut,mem_above]
    constructor
    · intro hc
      exact r.trans hc hr
    · intro hc
      have H : r (some c) (some a) = true := hc
      rcases r.total (by simp : (some c : Option α) ≠ none) with hc | hc
      · exact hc
      · exact False.elim (hcon (some c) ⟨hc,H⟩)
  have hra : r (some a) none = false := by
    rw [r.reverse_comparison (by simp : (none : Option α) ≠ some a),hr]
    rfl
  have hsa : s (some a) none = true := by
    rw [s.reverse_comparison (by simp : (none : Option α) ≠ some a),hs]
    rfl
  have hcutS : s.insertionCut = insert a r.insertionCut := by
    ext c
    simp only [mem_insertionCut,Finset.mem_insert]
    by_cases hca : c = a
    · subst c
      simp [hsa]
    · have H : r (some c) none = s (some c) none :=
        hoff (some c) none (by simp) (by simpa using hca)
      simp [hca,H]
  let t := P.rankIndex a
  have hslotR : r.insertionSlot = t.castSucc := by
    apply Fin.ext
    change r.insertionCut.card = P.rank a
    rw [hcut]
    rfl
  have hslotS : s.insertionSlot = t.succ := by
    apply Fin.ext
    change s.insertionCut.card = P.rank a + 1
    rw [hcutS,Finset.card_insert_of_notMem]
    · rw [hcut]
      rfl
    · simpa [mem_insertionCut,hra]
  refine ⟨P,t,?_,?_⟩
  · have H := r.reconstruct_insertion
    rw [hslotR] at H
    exact H.symm
  · have H := s.reconstruct_insertion
    rw [hrest,hslotS] at H
    exact H.symm

end Order

/-- Every actual directed adjacent swap has an occupied-consecutive-slot
representation with the upper swapped alternative distinguished. -/
theorem AdjacentSwap.exists_slots {n : Nat} {r s : Order (Fin (n+1))}
    (h : AdjacentSwap r s) :
    ∃ (x : Fin (n+1)) (P : Order (Fin n)) (t : Fin (Fintype.card (Fin n))),
      r = labelledInsertion x P t.castSucc ∧ s = labelledInsertion x P t.succ := by
  obtain ⟨a,b,hab,hr,hs,hcon,hoff⟩ := h
  let e := deletionEquiv a
  have hb : e.symm b ≠ none := by
    intro H
    have := congrArg e H
    simp only [Equiv.apply_symm_apply] at this
    exact hab this.symm
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hb
  let r' := Order.transport e.symm r
  let s' := Order.transport e.symm s
  have he : e (some c) = b := by rw [← hc]; exact e.apply_symm_apply b
  have h₁ : r' none (some c) = true := by
    change r (e none) (e (some c)) = true
    simpa [e,he] using hr
  have h₂ : s' none (some c) = false := by
    change s (e none) (e (some c)) = false
    simpa [e,he] using hs
  have h₃ : ∀ u, ¬(r' none u = true ∧ r' u (some c) = true) := by
    intro u
    change ¬(r (e none) (e u) = true ∧ r (e u) (e (some c)) = true)
    simpa [e,he] using hcon (e u)
  have h₄ : ∀ u v, (u,v) ≠ (none,some c) → (u,v) ≠ (some c,none) → r' u v = s' u v := by
    intro u v h₁ h₂
    apply hoff (e u) (e v)
    · intro H
      apply h₁
      apply Prod.ext
      · apply e.injective
        exact congrArg Prod.fst H
      · apply e.injective
        exact (congrArg Prod.snd H).trans he.symm
    · intro H
      apply h₂
      apply Prod.ext
      · apply e.injective
        exact (congrArg Prod.fst H).trans he.symm
      · apply e.injective
        exact congrArg Prod.snd H
  obtain ⟨P,t,hr',hs'⟩ := Order.swap_none_slots r' s' c h₁ h₂ h₃ h₄
  refine ⟨a,P,t,?_,?_⟩
  · have H := congrArg (Order.transport e) hr'
    simpa [r',labelledInsertion,e] using H
  · have H := congrArg (Order.transport e) hs'
    simpa [s',labelledInsertion,e] using H

#print axioms Order.swap_none_slots
#print axioms AdjacentSwap.exists_slots
/-- The oriented pair changed by a directed adjacent swap is unique. -/
theorem changed_upper_unique {α : Type*} (r s : Order α) (a b c d : α)
    (hab : r a b = true) (hsab : s a b = false) (hcd : r c d = true)
    (hoff : ∀ u v, (u,v) ≠ (c,d) → (u,v) ≠ (d,c) → r u v = s u v) : a = c := by
  by_cases h₁ : (a,b) = (c,d)
  · exact congrArg Prod.fst h₁
  · by_cases h₂ : (a,b) = (d,c)
    · have ha : a = d := congrArg Prod.fst h₂
      have hb : b = c := congrArg Prod.snd h₂
      have H := r.trans hcd (show r d c = true from by simpa [ha,hb] using hab)
      rw [r.irrefl] at H
      contradiction
    · have H := hoff a b h₁ h₂
      rw [hab,hsab] at H
      contradiction

theorem labelledInsertion_changed {n : Nat} (x : Fin (n+1)) (P : Order (Fin n))
    (t : Fin (Fintype.card (Fin n))) :
    ∃ b, labelledInsertion x P t.castSucc x b = true ∧
      labelledInsertion x P t.succ x b = false ∧
      (∀ u v, (u,v) ≠ (x,b) → (u,v) ≠ (b,x) →
        labelledInsertion x P t.castSucc u v = labelledInsertion x P t.succ u v) := by
  let e := deletionEquiv x
  let b := e (some (P.atPosition t))
  refine ⟨b,?_,?_,?_⟩
  · change P.insertAt t.castSucc (e.symm (e none)) (e.symm (e (some (P.atPosition t)))) = true
    simp only [Equiv.symm_apply_apply]
    change decide (t.val ≤ P.rank (P.atPosition t)) = true
    simp
  · change P.insertAt t.succ (e.symm (e none)) (e.symm (e (some (P.atPosition t)))) = false
    simp only [Equiv.symm_apply_apply]
    change decide (t.val+1 ≤ P.rank (P.atPosition t)) = false
    simp
  · intro u v h₁ h₂
    apply P.insertAt_step_agree t (e.symm u) (e.symm v)
    · intro h
      apply h₁
      have H := congrArg (Prod.map e e) h
      simpa [b,e] using H
    · intro h
      apply h₂
      have H := congrArg (Prod.map e e) h
      simpa [b,e] using H

abbrev SlotIndex (n : Nat) := Fin (n+1) × Order (Fin n) × Fin (Fintype.card (Fin n))

noncomputable def slotOrders {n : Nat} (v : SlotIndex n) :
    Order (Fin (n+1)) × Order (Fin (n+1)) :=
  (labelledInsertion v.1 v.2.1 v.2.2.castSucc, labelledInsertion v.1 v.2.1 v.2.2.succ)

theorem slotOrders_injective (n : Nat) : Function.Injective (@slotOrders n) := by
  rintro ⟨x,P,t⟩ ⟨y,Q,u⟩ h
  have hr : labelledInsertion x P t.castSucc = labelledInsertion y Q u.castSucc :=
    congrArg Prod.fst h
  have hs : labelledInsertion x P t.succ = labelledInsertion y Q u.succ :=
    congrArg Prod.snd h
  obtain ⟨b,hb₁,hb₂,_⟩ := labelledInsertion_changed x P t
  obtain ⟨c,hc₁,_,hoff⟩ := labelledInsertion_changed y Q u
  rw [hr] at hb₁
  rw [hs] at hb₂
  have hxy := changed_upper_unique _ _ x b y c hb₁ hb₂ hc₁ hoff
  subst y
  have hPQ : P.insertAt t.castSucc = Q.insertAt u.castSucc :=
    Order.transport_injective (deletionEquiv x) hr
  have heq : P = Q := by
    have H := congrArg (Order.restrict Order.someEmbedding) hPQ
    simpa using H
  subst Q
  have htu := P.insertAt_injective hPQ
  have htu' : t = u := Fin.ext (congrArg (fun v : Fin (Fintype.card (Fin n)+1) => v.val) htu)
  subst u
  rfl

/-- Directed edges of the actual adjacent-swap graph. Each undirected edge
occurs in both directions, as in the paper's statistic A. -/
noncomputable def directedEdges {n : Nat} (D : Domain (Fin n)) :
    Finset (Order (Fin n) × Order (Fin n)) := by
  classical
  exact (D.product D).filter (fun rs => AdjacentSwap rs.1 rs.2)

noncomputable def adjacencyCount {n : Nat} (D : Domain (Fin n)) : Nat :=
  (directedEdges D).card

noncomputable def slotEdges {n : Nat} (D : Domain (Fin (n+1))) : Finset (SlotIndex n) := by
  classical
  exact Finset.univ.filter (fun v => (slotOrders v).1 ∈ D ∧ (slotOrders v).2 ∈ D)

theorem image_slotEdges {n : Nat} (D : Domain (Fin (n+1))) :
    (slotEdges D).image slotOrders = directedEdges D := by
  classical
  ext rs
  constructor
  · intro h
    obtain ⟨⟨x,P,t⟩,hv,rfl⟩ := Finset.mem_image.mp h
    have hm := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hm,labelledInsertion_adjacent x P t⟩
  · intro h
    obtain ⟨hm,hadj⟩ := Finset.mem_filter.mp h
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hm
    obtain ⟨x,P,t,h₁,h₂⟩ := hadj.exists_slots
    refine Finset.mem_image.mpr ⟨(x,P,t),?_,Prod.ext h₁.symm h₂.symm⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · change labelledInsertion x P t.castSucc ∈ D
      rw [← h₁]
      exact hr
    · change labelledInsertion x P t.succ ∈ D
      rw [← h₂]
      exact hs

theorem card_slotEdges {n : Nat} (D : Domain (Fin (n+1))) :
    (slotEdges D).card = slotAdjacencyCount D := by
  classical
  rw [slotAdjacencyCount_eq_sum]
  simp only [slotEdges,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.univ_product_univ,Finset.sum_product]
  rfl

/-- The exact identification of insertion-slot edges with the paper's A(D). -/
theorem slotAdjacencyCount_eq_adjacencyCount {n : Nat} (D : Domain (Fin (n+1))) :
    slotAdjacencyCount D = adjacencyCount D := by
  rw [← card_slotEdges,adjacencyCount,← image_slotEdges,
    Finset.card_image_of_injective _ (slotOrders_injective n)]

/-- The global deletion-gap identity, now with actual directed adjacent swaps. -/
theorem deletion_gap_adjacency_identity {n : Nat} (D : Domain (Fin (n+1))) :
    deletionSum D + gapCount D + adjacencyCount D = (n+1) * D.card := by
  simpa only [slotAdjacencyCount_eq_adjacencyCount] using global_fibre_run_identity D

#print axioms slotOrders_injective
#print axioms image_slotEdges
#print axioms slotAdjacencyCount_eq_adjacencyCount
#print axioms deletion_gap_adjacency_identity

end Condorcet
