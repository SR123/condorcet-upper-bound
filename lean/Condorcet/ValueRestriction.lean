import Condorcet.Majority

namespace Condorcet

/-- Two strict-majority sets of voters intersect. -/
theorem majority_sets_intersect {m : Nat} (S T : Finset (Fin m))
    (hS : 2 * S.card > m) (hT : 2 * T.card > m) : ∃ i, i ∈ S ∧ i ∈ T := by
  classical
  by_contra h
  have hd : Disjoint S T := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact h ⟨i, hi, hj⟩)
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_union_of_disjoint hd] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem majority_irrefl {α : Type*} {m : Nat} (v : Fin m → Order α) (a : α) :
    ¬ majority v a a := by
  simp [majority, Order.irrefl]

theorem majority_asymm {α : Type*} {m : Nat} (v : Fin m → Order α) {a b : α}
    (hab : majority v a b) : ¬ majority v b a := by
  intro hba
  obtain ⟨i, hi, hj⟩ := majority_sets_intersect _ _ hab hba
  have ha : v i a b = true := (Finset.mem_filter.mp hi).2
  have hb : v i b a = true := (Finset.mem_filter.mp hj).2
  rw [(v i).asymmetric ha] at hb
  contradiction

/-- Oddness removes pairwise majority ties. -/
theorem majority_total {α : Type*} {m : Nat} (v : Fin m → Order α)
    (hm : Odd m) {a b : α} (hab : a ≠ b) : majority v a b ∨ majority v b a := by
  classical
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin m))) (fun i => v i a b = true)
  have hn : (Finset.univ.filter (fun i => ¬v i a b = true)) =
      (Finset.univ.filter (fun i => v i b a = true)) := by
    apply Finset.filter_congr
    intro i _
    rw [(v i).reverse_comparison hab]
    cases v i a b <;> decide
  rw [hn] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  rcases hm with ⟨k, hk⟩
  by_cases h : majority v a b
  · exact Or.inl h
  · right
    unfold majority at *
    omega

theorem majority_imp {α : Type*} {m : Nat} (v : Fin m → Order α) {a b c d : α}
    (h : ∀ i, v i a b = true → v i c d = true) : majority v a b → majority v c d := by
  intro hab
  have hs : (Finset.univ.filter (fun i => v i a b = true)) ⊆
      (Finset.univ.filter (fun i => v i c d = true)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i (Finset.mem_filter.mp hi).2⟩
  have hc := Finset.card_le_card hs
  unfold majority at *
  omega

theorem Never.swap {α : Type*} (r : Order α) (x y z : α) (p : Fin 3) :
    Never r x y z p ↔ Never r x z y p := by
  fin_cases p
  · exact or_comm
  · exact eq_comm
  · exact or_comm

/-- A common never-position clause rules out a directed majority triangle.
This uses transitivity of every input order, not just Boolean clause preservation. -/
theorem common_never_excludes_majority_cycle {α : Type*} {m : Nat}
    (v : Fin m → Order α) {x y z : α} (hxz : x ≠ z) (p : Fin 3)
    (hn : ∀ i, Never (v i) x y z p)
    (hxy : majority v x y) (hyz : majority v y z) (hzx : majority v z x) : False := by
  fin_cases p
  · have hzy : majority v z y := majority_imp v (by
      intro i hi
      have H := hn i
      simp only [Never, ↓reduceIte] at H
      have hxzf : v i x z = false := H.resolve_left (by simp [hi])
      have hzxt : v i z x = true := ((v i).total hxz).resolve_left (by simp [hxzf])
      exact (v i).trans hzxt hi) hxy
    exact majority_asymm v hyz hzy
  · have hxzt : majority v x z := majority_imp v (by
      intro i hi
      have H := hn i
      simp only [Never, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at H
      rw [← H]
      exact hi) hxy
    exact majority_asymm v hxzt hzx
  · have hzy : majority v z y := majority_imp v (by
      intro i hi
      have H := hn i
      simp only [Never, show (2 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at H
      have hxzf := (v i).asymmetric hi
      have hxyt := H.resolve_right (by simp [hxzf])
      exact (v i).trans hi hxyt) hzx
    exact majority_asymm v hyz hzy

/-- One direction of the actual Condorcet-domain characterization. -/
theorem ValueRestricted.isCondorcet {α : Type*} {D : Domain α}
    (hD : ValueRestricted D) : IsCondorcet D := by
  intro m hm v hv a b c hab hbc
  by_contra hac
  have habne : a ≠ b := by
    intro h; subst b
    exact majority_irrefl v a hab
  have hbcne : b ≠ c := by
    intro h; subst c
    exact majority_irrefl v b hbc
  have hacne : a ≠ c := by
    intro h; subst c
    exact majority_asymm v hab hbc
  have hca : majority v c a := (majority_total v hm hacne).resolve_left hac
  obtain ⟨p, hp⟩ := hD a b c habne hacne hbcne
  rcases hp with hp | hp | hp
  · exact common_never_excludes_majority_cycle v hacne p (fun i => hp _ (hv i)) hab hbc hca
  · exact common_never_excludes_majority_cycle v (Ne.symm habne) p
      (fun i => (Never.swap _ _ _ _ _).mp (hp _ (hv i))) hbc hca hab
  · exact common_never_excludes_majority_cycle v (Ne.symm hbcne) p
      (fun i => hp _ (hv i)) hca hab hbc

theorem ExtremeRestricted.valueRestricted {α : Type*} {D : Domain α}
    (hD : ExtremeRestricted D) : ValueRestricted D := by
  intro a b c hab hac hbc
  obtain ⟨p, _, hp⟩ := hD a b c hab hac hbc
  exact ⟨p, hp⟩

theorem ExtremeRestricted.isPeakPit {α : Type*} {D : Domain α}
    (hD : ExtremeRestricted D) : IsPeakPit D :=
  ⟨hD.valueRestricted.isCondorcet, hD⟩

#print axioms ValueRestricted.isCondorcet
#print axioms ExtremeRestricted.isPeakPit
end Condorcet
