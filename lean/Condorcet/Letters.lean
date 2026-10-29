import Condorcet.MissingSwap

namespace Condorcet
namespace Order

/-- The adjacent pair p immediately above q in an actual order. -/
def Consecutive {α : Type*} (r : Order α) (p q : α) : Prop :=
  p ≠ q ∧ r p q = true ∧ ∀ c, ¬(r p c = true ∧ r c q = true)

noncomputable def swapLabels {α : Type*} (r : Order α) (p q : α) : Order α := by
  classical
  exact restrict (Equiv.swap p q).toEmbedding r

@[simp] theorem swapLabels_apply {α : Type*} [DecidableEq α] (r : Order α) (p q a b : α) :
    r.swapLabels p q a b = r (Equiv.swap p q a) (Equiv.swap p q b) := by
  classical
  by_cases h₁ : a = p <;> by_cases h₂ : a = q <;>
    by_cases h₃ : b = p <;> by_cases h₄ : b = q <;>
    simp [swapLabels,Equiv.swap_apply_def,h₁,h₂,h₃,h₄]

theorem Consecutive.above_agree {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) (z : α) (hzp : z ≠ p) (hzq : z ≠ q) : r p z = r q z := by
  cases hp : r p z <;> cases hq : r q z
  · rfl
  · have H := r.trans h.2.1 hq
    rw [hp] at H
    contradiction
  · have H : r z q = true := (r.total hzq).resolve_right (by simp [hq])
    exact False.elim (h.2.2 z ⟨hp,H⟩)
  · rfl

theorem Consecutive.below_agree {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) (z : α) (hzp : z ≠ p) (hzq : z ≠ q) : r z p = r z q := by
  rw [r.reverse_comparison hzp.symm,r.reverse_comparison hzq.symm,h.above_agree z hzp hzq]

theorem Consecutive.swap_agree {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) (a b : α) (hab : (a,b) ≠ (p,q)) (hba : (a,b) ≠ (q,p)) :
    r a b = r.swapLabels p q a b := by
  classical
  by_cases hap : a = p
  · subst a
    by_cases hbp : b = p
    · subst b
      simp [swapLabels,irrefl]
    · have hbq : b ≠ q := fun H => hab (Prod.ext rfl H)
      simpa [Equiv.swap_apply_def,hbp,hbq] using h.above_agree b hbp hbq
  · by_cases haq : a = q
    · subst a
      by_cases hbq : b = q
      · subst b
        simp [swapLabels,irrefl]
      · have hbp : b ≠ p := fun H => hba (Prod.ext rfl H)
        simpa [Equiv.swap_apply_def,hbp,hbq] using (h.above_agree b hbp hbq).symm
    · by_cases hbp : b = p
      · subst b
        simpa [Equiv.swap_apply_def,hap,haq] using h.below_agree a hap haq
      · by_cases hbq : b = q
        · subst b
          simpa [Equiv.swap_apply_def,hap,haq] using (h.below_agree a hap haq).symm
        · simp [Equiv.swap_apply_def,hap,haq,hbp,hbq]

theorem Consecutive.swapped_comparison {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) : r.swapLabels p q p q = false := by
  classical
  simpa using r.asymmetric h.2.1

theorem Consecutive.swapped_reverse {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) : (r.swapLabels p q).Consecutive q p := by
  classical
  refine ⟨h.1.symm,?_,?_⟩
  · simpa using h.2.1
  · intro c ⟨hqc,hcp⟩
    by_cases hcq : c = q
    · subst c
      rw [irrefl] at hqc
      contradiction
    · by_cases hcp' : c = p
      · subst c
        rw [irrefl] at hcp
        contradiction
      · have H₁ : r p c = true := by simpa [Equiv.swap_apply_def,hcq,hcp'] using hqc
        have H₂ : r c q = true := by simpa [Equiv.swap_apply_def,hcq,hcp'] using hcp
        exact h.2.2 c ⟨H₁,H₂⟩

noncomputable def positionEquiv {n : Nat} (r : Order (Fin (n+1))) : Fin (n+1) ≃ Fin (n+1) :=
  r.rankEquiv.trans (finCongr (Fintype.card_fin (n+1)))

noncomputable def atPos {n : Nat} (r : Order (Fin (n+1))) (i : Fin (n+1)) : Fin (n+1) :=
  r.positionEquiv.symm i

@[simp] theorem rank_atPos {n : Nat} (r : Order (Fin (n+1))) (i : Fin (n+1)) :
    r.rank (r.atPos i) = i.val := by
  have H := congrArg Fin.val (r.positionEquiv.apply_symm_apply i)
  exact H

@[simp] theorem positionEquiv_val {n : Nat} (r : Order (Fin (n+1))) (a : Fin (n+1)) :
    (r.positionEquiv a).val = r.rank a := rfl

theorem atPos_consecutive {n : Nat} (r : Order (Fin (n+1))) (j : Fin n) :
    r.Consecutive (r.atPos j.castSucc) (r.atPos j.succ) := by
  have H₁ : r.rank (r.atPos j.castSucc) = j.val := r.rank_atPos _
  have H₂ : r.rank (r.atPos j.succ) = j.val+1 := r.rank_atPos _
  refine ⟨?_,r.rank_lt_iff.mp (by omega),?_⟩
  · intro h
    rw [h] at H₁
    omega
  · intro c ⟨hp,hq⟩
    have hc₁ := r.rank_lt_of_above hp
    have hc₂ := r.rank_lt_of_above hq
    omega

end Order

theorem Order.Consecutive.adjacentSwap {n : Nat} {r : Order (Fin n)} {p q : Fin n}
    (h : r.Consecutive p q) : AdjacentSwap r (r.swapLabels p q) :=
  ⟨p,q,h.1,h.2.1,h.swapped_comparison,h.2.2,h.swap_agree⟩

/-- Actual adjacent-swap letter j of r, expressed through its ranked alternatives. -/
noncomputable def swapLetter {n : Nat} (r : Order (Fin (n+1))) (j : Fin n) : Order (Fin (n+1)) :=
  r.swapLabels (r.atPos j.castSucc) (r.atPos j.succ)

theorem swapLetter_adjacent {n : Nat} (r : Order (Fin (n+1))) (j : Fin n) :
    AdjacentSwap r (swapLetter r j) := (r.atPos_consecutive j).adjacentSwap

#print axioms Order.Consecutive.swap_agree
#print axioms Order.atPos_consecutive
#print axioms swapLetter_adjacent
namespace Order

theorem rank_injective {α : Type*} [Fintype α] (r : Order α) : Function.Injective r.rank := by
  intro a b h
  exact r.rankIndex_injective (Fin.ext h)

theorem Consecutive.rank_succ {α : Type*} [Fintype α] {r : Order α} {p q : α}
    (h : r.Consecutive p q) : r.rank q = r.rank p + 1 := by
  have hlt := r.rank_lt_of_above h.2.1
  have hq := r.rank_lt_size q
  by_contra H
  have hp : r.rank p + 1 < Fintype.card α := by omega
  let c := r.atPosition ⟨r.rank p+1,hp⟩
  have hc : r.rank c = r.rank p+1 := r.rank_atPosition _
  exact h.2.2 c ⟨r.rank_lt_iff.mp (by omega),r.rank_lt_iff.mp (by omega)⟩

theorem Consecutive.swap_unique {α : Type*} {r : Order α} {p q : α}
    (h : r.Consecutive p q) (s : Order α) (hs : s p q = false)
    (hoff : ∀ a b, (a,b) ≠ (p,q) → (a,b) ≠ (q,p) → r a b = s a b) :
    r.swapLabels p q = s := by
  ext a b
  by_cases hab : (a,b) = (p,q)
  · have ha : a = p := congrArg Prod.fst hab
    have hb : b = q := congrArg Prod.snd hab
    rw [ha,hb,h.swapped_comparison,hs]
  · by_cases hba : (a,b) = (q,p)
    · have ha : a = q := congrArg Prod.fst hba
      have hb : b = p := congrArg Prod.snd hba
      rw [ha,hb,(r.swapLabels p q).reverse_comparison h.1,s.reverse_comparison h.1,
        h.swapped_comparison,hs]
    · exact (h.swap_agree a b hab hba).symm.trans (hoff a b hab hba)

end Order

theorem AdjacentSwap.exists_letter {n : Nat} {r s : Order (Fin (n+1))}
    (h : AdjacentSwap r s) : ∃ j : Fin n, swapLetter r j = s := by
  obtain ⟨p,q,hpq,hr,hs,hcon,hoff⟩ := h
  have hc : r.Consecutive p q := ⟨hpq,hr,hcon⟩
  have hq := r.rank_lt_size q
  simp only [Fintype.card_fin] at hq
  have hrank := hc.rank_succ
  let j : Fin n := ⟨r.rank p,by omega⟩
  have hpj : r.atPos j.castSucc = p := r.rank_injective (by simp [j])
  have hqj : r.atPos j.succ = q := r.rank_injective (by simp [j,hrank])
  refine ⟨j,?_⟩
  simpa only [swapLetter,hpj,hqj] using hc.swap_unique s hs hoff

theorem swapLetter_injective {n : Nat} (r : Order (Fin (n+1))) : Function.Injective (swapLetter r) := by
  intro j k h
  have hj := r.atPos_consecutive j
  have hk := r.atPos_consecutive k
  have hs : swapLetter r k (r.atPos j.castSucc) (r.atPos j.succ) = false := by
    rw [← h]
    exact hj.swapped_comparison
  have H := changed_upper_unique r (swapLetter r k)
    (r.atPos j.castSucc) (r.atPos j.succ) (r.atPos k.castSucc) (r.atPos k.succ)
    hj.2.1 hs hk.2.1 hk.swap_agree
  apply Fin.ext
  have Hrank := congrArg r.rank H
  simpa only [Order.rank_atPos,Fin.val_castSucc] using Hrank

noncomputable def letterEdges {n : Nat} (D : Domain (Fin (n+1))) :
    Finset (Order (Fin (n+1)) × Fin n) := by
  classical
  exact (D.product Finset.univ).filter (fun v => swapLetter v.1 v.2 ∈ D)

noncomputable def letterOrders {n : Nat} (v : Order (Fin (n+1)) × Fin n) :
    Order (Fin (n+1)) × Order (Fin (n+1)) := (v.1,swapLetter v.1 v.2)

theorem letterOrders_injective (n : Nat) : Function.Injective (@letterOrders n) := by
  rintro ⟨r,j⟩ ⟨s,k⟩ h
  have hrs : r = s := congrArg Prod.fst h
  subst s
  have hjk : swapLetter r j = swapLetter r k := congrArg Prod.snd h
  have H := swapLetter_injective r hjk
  subst k
  rfl

theorem image_letterEdges {n : Nat} (D : Domain (Fin (n+1))) :
    (letterEdges D).image letterOrders = directedEdges D := by
  classical
  ext rs
  constructor
  · intro h
    obtain ⟨⟨r,j⟩,hv,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hm,hs⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm).1,hs⟩,
      swapLetter_adjacent r j⟩
  · intro h
    obtain ⟨hm,h⟩ := Finset.mem_filter.mp h
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hm
    obtain ⟨j,hj⟩ := h.exists_letter
    refine Finset.mem_image.mpr ⟨(rs.1,j),?_,Prod.ext rfl hj⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,Finset.mem_univ _⟩,by simpa [hj] using hs⟩

/-- A(D) counts exactly the enabled adjacent letters (order,position). -/
theorem adjacencyCount_eq_letters {n : Nat} (D : Domain (Fin (n+1))) :
    adjacencyCount D = ∑ r ∈ D, ∑ j : Fin n, if swapLetter r j ∈ D then 1 else 0 := by
  classical
  rw [adjacencyCount,← image_letterEdges,Finset.card_image_of_injective _ (letterOrders_injective n)]
  simp only [letterEdges,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_product D Finset.univ (fun v => if swapLetter v.1 v.2 ∈ D then (1 : Nat) else 0)

#print axioms Order.Consecutive.rank_succ
#print axioms AdjacentSwap.exists_letter
#print axioms swapLetter_injective
#print axioms adjacencyCount_eq_letters

end Condorcet
