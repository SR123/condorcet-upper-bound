import Condorcet.DirectedAdjacency

namespace Condorcet

/-- On a triple containing a globally fixed pair, a single-pair swap can be
adjoined while retaining an extreme common law. -/
theorem fixed_pair_common_after_swap {α : Type*} {D : Domain α} (r s : Order α)
    (p q z : α) (hpz : p ≠ z) (hqz : q ≠ z)
    (hr : r ∈ D) (hfixed : ∀ u ∈ D, u p q = true)
    (hoff : ∀ u v, (u,v) ≠ (p,q) → (u,v) ≠ (q,p) → r u v = s u v) :
    CommonLaw (insert s D) p q z := by
  classical
  by_cases hq : r q z = true
  · have hp : r p z = true := r.trans (hfixed r hr) hq
    have hs : s p z = true := by
      rw [← hoff p z (fun h => hqz (congrArg Prod.snd h).symm) (fun h => hpz (congrArg Prod.snd h).symm)]
      exact hp
    refine ⟨2,Or.inl ?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · simp [Never,hs]
    · simp [Never,hfixed u hu]
  · have hq' : r q z = false := Bool.eq_false_iff.mpr hq
    have hs : s q z = false := by
      rw [← hoff q z (fun h => hqz (congrArg Prod.snd h).symm) (fun h => hpz (congrArg Prod.snd h).symm)]
      exact hq'
    refine ⟨0,Or.inr (Or.inl ?_)⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · simp [Never,hs]
    · have H := u.asymmetric (hfixed u hu)
      simp [Never,H]

/-- Swapping a globally fixed pair preserves the semantic Condorcet property
when every other comparison is unchanged. -/
theorem IsCondorcet.insert_fixed_swap {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    (r s : Order α) (p q : α) (hpq : p ≠ q) (hr : r ∈ D)
    (hfixed : ∀ u ∈ D, u p q = true)
    (hoff : ∀ u v, (u,v) ≠ (p,q) → (u,v) ≠ (q,p) → r u v = s u v) :
    IsCondorcet (insert s D) := by
  classical
  apply ValueRestricted.isCondorcet
  intro a b c hab hac hbc
  change CommonLaw (insert s D) a b c
  by_cases hp : p = a ∨ p = b ∨ p = c
  · by_cases hq : q = a ∨ q = b ∨ q = c
    · rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> subst p <;> subst q
      · exact False.elim (hpq rfl)
      · exact fixed_pair_common_after_swap r s a b c hac hbc hr hfixed hoff
      · exact (fixed_pair_common_after_swap r s a c b hab hbc.symm hr hfixed hoff).swap23
      · exact (fixed_pair_common_after_swap r s b a c hbc hac hr hfixed hoff).swap12
      · exact False.elim (hpq rfl)
      · exact (fixed_pair_common_after_swap r s b c a hab.symm hac.symm hr hfixed hoff).swap23.swap12
      · exact (fixed_pair_common_after_swap r s c a b hbc.symm hab hr hfixed hoff).swap12.swap23
      · exact (fixed_pair_common_after_swap r s c b a hac.symm hab.symm hr hfixed hoff).swap12.swap23.swap12
      · exact False.elim (hpq rfl)
    · have H : ∀ x y, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) → r x y = s x y := by
        intro x y hx hy
        apply hoff x y
        · intro heq
          exact hq ((show y = q from congrArg Prod.snd heq) ▸ hy)
        · intro heq
          exact hq ((show x = q from congrArg Prod.fst heq) ▸ hx)
      obtain ⟨j,hj⟩ := hD.valueRestricted a b c hab hac hbc
      have lift : ∀ x y z, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
          (z = a ∨ z = b ∨ z = c) → (∀ u ∈ D, Never u x y z j) →
          ∀ u ∈ insert s D, Never u x y z j := by
        intro x y z hx hy hz hl u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · simpa only [Never,← H x y hx hy,← H x z hx hz] using hl r hr
        · exact hl u hu
      refine ⟨j,?_⟩
      rcases hj with hj | hj | hj
      · exact Or.inl (lift a b c (by simp) (by simp) (by simp) hj)
      · exact Or.inr (Or.inl (lift b a c (by simp) (by simp) (by simp) hj))
      · exact Or.inr (Or.inr (lift c a b (by simp) (by simp) (by simp) hj))
  · have H : ∀ x y, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) → r x y = s x y := by
      intro x y hx hy
      apply hoff x y
      · intro heq
        exact hp ((show x = p from congrArg Prod.fst heq) ▸ hx)
      · intro heq
        exact hp ((show y = p from congrArg Prod.snd heq) ▸ hy)
    obtain ⟨j,hj⟩ := hD.valueRestricted a b c hab hac hbc
    have lift : ∀ x y z, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
        (z = a ∨ z = b ∨ z = c) → (∀ u ∈ D, Never u x y z j) →
        ∀ u ∈ insert s D, Never u x y z j := by
      intro x y z hx hy hz hl u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simpa only [Never,← H x y hx hy,← H x z hx hz] using hl r hr
      · exact hl u hu
    refine ⟨j,?_⟩
    rcases hj with hj | hj | hj
    · exact Or.inl (lift a b c (by simp) (by simp) (by simp) hj)
    · exact Or.inr (Or.inl (lift b a c (by simp) (by simp) (by simp) hj))
    · exact Or.inr (Or.inr (lift c a b (by simp) (by simp) (by simp) hj))

/-- Maximality forbids an adjacent exchange of a globally fixed pair. -/
theorem IsMaximal.no_fixed_pair_swap {α : Type*} {D : Domain α} (hD : IsMaximal D)
    (r s : Order α) (p q : α) (hpq : p ≠ q) (hr : r ∈ D)
    (hfixed : ∀ u ∈ D, u p q = true) (hs : s p q = false)
    (hoff : ∀ u v, (u,v) ≠ (p,q) → (u,v) ≠ (q,p) → r u v = s u v) : False := by
  classical
  have hIns := hD.1.insert_fixed_swap r s p q hpq hr hfixed hoff
  have heq := hD.2 _ hIns (Finset.subset_insert _ _)
  have hmem : s ∈ D := by rw [← heq]; exact Finset.mem_insert_self _ _
  have H := hfixed s hmem
  rw [hs] at H
  contradiction

#print axioms IsCondorcet.insert_fixed_swap
#print axioms IsMaximal.no_fixed_pair_swap
namespace Order

theorem consecutive_none_insertion {α : Type*} [Fintype α] (r : Order (Option α)) (a : α)
    (hr : r none (some a) = true)
    (hcon : ∀ c, ¬(r none c = true ∧ r c (some a) = true)) :
    r = (restrict someEmbedding r).insertAt
      ((restrict someEmbedding r).rankIndex a).castSucc := by
  let P := restrict someEmbedding r
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
  have hslot : r.insertionSlot = (P.rankIndex a).castSucc := by
    apply Fin.ext
    change r.insertionCut.card = P.rank a
    rw [hcut]
    rfl
  have H := r.reconstruct_insertion
  rw [hslot] at H
  exact H.symm

end Order

/-- Paper Lemma 3.4: in a maximal CD, a globally fixed comparison is never
realised by consecutive alternatives in any member. -/
theorem IsMaximal.fixed_pair_not_consecutive {n : Nat} {D : Domain (Fin (n+1))}
    (hD : IsMaximal D) (r : Order (Fin (n+1))) (p q : Fin (n+1))
    (hpq : p ≠ q) (hr : r ∈ D) (hfixed : ∀ u ∈ D, u p q = true) :
    ¬(∀ c, ¬(r p c = true ∧ r c q = true)) := by
  intro hcon
  let e := deletionEquiv p
  have hq : e.symm q ≠ none := by
    intro H
    have := congrArg e H
    simp only [Equiv.apply_symm_apply] at this
    exact hpq this.symm
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hq
  have he : e (some c) = q := by rw [← hc]; exact e.apply_symm_apply q
  let r' := Order.transport e.symm r
  let P := Order.restrict Order.someEmbedding r'
  let t := P.rankIndex c
  have h₁ : r' none (some c) = true := by
    change r (e none) (e (some c)) = true
    simpa [e,he] using hfixed r hr
  have h₂ : ∀ u, ¬(r' none u = true ∧ r' u (some c) = true) := by
    intro u
    change ¬(r (e none) (e u) = true ∧ r (e u) (e (some c)) = true)
    simpa [e,he] using hcon (e u)
  have hrepr : r = labelledInsertion p P t.castSucc := by
    have H := congrArg (Order.transport e) (Order.consecutive_none_insertion r' c h₁ h₂)
    simpa [r',P,t,labelledInsertion,e] using H
  have hchanged := labelledInsertion_changed p P t
  obtain ⟨b,hb₁,hb₂,hoff⟩ := hchanged
  have hbq : b = q := by
    have hq₁ : labelledInsertion p P t.castSucc p q = true := hrepr ▸ hfixed r hr
    have hq₂ : labelledInsertion p P t.succ p q = false := by
      change P.insertAt t.succ (e.symm (e none)) (e.symm q) = false
      rw [Equiv.symm_apply_apply,hc]
      change decide (P.rank c + 1 ≤ P.rank c) = false
      simp
    by_contra hbq
    have H := hoff p q (fun h => hbq (congrArg Prod.snd h).symm)
      (fun h => hpq (congrArg Prod.snd h).symm)
    rw [hq₁,hq₂] at H
    contradiction
  subst b
  apply hD.no_fixed_pair_swap r (labelledInsertion p P t.succ) p q hpq hr hfixed hb₂
  intro u v h₃ h₄
  rw [hrepr]
  exact hoff u v h₃ h₄

#print axioms Order.consecutive_none_insertion
#print axioms IsMaximal.fixed_pair_not_consecutive

end Condorcet
