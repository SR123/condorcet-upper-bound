import Condorcet.FullDomains

namespace Condorcet

def CommonExtremeLaw {α : Type*} (D : Domain α) (a b c : α) : Prop :=
  ∃ p : Fin 3, p ≠ 1 ∧ ((∀ r ∈ D, Never r a b c p) ∨
    (∀ r ∈ D, Never r b a c p) ∨ (∀ r ∈ D, Never r c a b p))

theorem CommonExtremeLaw.swap12 {α : Type*} {D : Domain α} {a b c : α}
    (H : CommonExtremeLaw D a b c) : CommonExtremeLaw D b a c := by
  obtain ⟨p,hp,H⟩ := H
  refine ⟨p,hp,?_⟩
  rcases H with H | H | H
  · exact Or.inr (Or.inl H)
  · exact Or.inl H
  · exact Or.inr (Or.inr (fun r hr => (Never.swap r c a b p).mp (H r hr)))

theorem CommonExtremeLaw.swap23 {α : Type*} {D : Domain α} {a b c : α}
    (H : CommonExtremeLaw D a b c) : CommonExtremeLaw D a c b := by
  obtain ⟨p,hp,H⟩ := H
  refine ⟨p,hp,?_⟩
  rcases H with H | H | H
  · exact Or.inl (fun r hr => (Never.swap r a b c p).mp (H r hr))
  · exact Or.inr (Or.inr H)
  · exact Or.inr (Or.inl H)

theorem sorted_extreme_implies_extremeRestricted {n : Nat} {D : Domain (Fin n)}
    (H : ∀ a b c : Fin n, a < b → b < c → CommonExtremeLaw D a b c) :
    ExtremeRestricted D := by
  intro a b c hab hac hbc
  change CommonExtremeLaw D a b c
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact H a b c hab hbc
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact (H a c b hac hcb).swap23
      · exact (H c a b hca hab).swap12.swap23
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact (H b a c hba hac).swap12
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact (H b c a hbc hca).swap23.swap12
      · exact (H c b a hcb hba).swap12.swap23.swap12

/-- One extreme never-law on every increasing triple. -/
def ExtremeSelection (n : Nat) := {L : Selection n // ∀ t, (L t).2 ≠ 1}

/-- Optional fixed comparison on each canonical unordered pair. -/
abbrev FixedPairs (n : Nat) := Pair n → Option Bool

def HoldsPairs {n : Nat} (Q : FixedPairs n) (r : Order (Fin n)) : Prop :=
  ∀ i b, Q i = some b → encode r i = b

/-- The full solution set of chosen extreme laws and fixed comparisons.
Nonemptiness is imposed separately by `InF`. -/
noncomputable def extremeFullDomain {n : Nat} (L : ExtremeSelection n)
    (Q : FixedPairs n) : Domain (Fin n) := by
  classical
  exact (fullDomain L.val).filter (HoldsPairs Q)

@[simp] theorem mem_extremeFullDomain {n : Nat} (L : ExtremeSelection n)
    (Q : FixedPairs n) (r : Order (Fin n)) :
    r ∈ extremeFullDomain L Q ↔ (∀ t, HoldsLaw r t (L.val t)) ∧ HoldsPairs Q r := by
  classical
  simp [extremeFullDomain]

def IsExtremeFull {n : Nat} (D : Domain (Fin n)) : Prop :=
  ∃ L : ExtremeSelection n, ∃ Q : FixedPairs n, D = extremeFullDomain L Q

/-- The paper's nonempty class of full extreme-law-plus-fixed-pair domains. -/
def InF {n : Nat} (D : Domain (Fin n)) : Prop := D.Nonempty ∧ IsExtremeFull D

theorem extreme_full_isPeakPit {n : Nat} (L : ExtremeSelection n) :
    IsPeakPit (fullDomain L.val) := by
  apply ExtremeRestricted.isPeakPit
  apply sorted_extreme_implies_extremeRestricted
  intro a b c hab hbc
  let t : Triple n := ⟨(a,b,c),hab,hbc⟩
  have H : ∀ r ∈ fullDomain L.val, HoldsLaw r t (L.val t) :=
    fun r hr => (mem_fullDomain L.val r).mp hr t
  rcases hEq : L.val t with ⟨x,p⟩
  have hp : p ≠ 1 := by simpa [hEq] using L.property t
  rw [hEq] at H
  refine ⟨p,hp,?_⟩
  fin_cases x
  · exact Or.inl H
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr H)

theorem ExtremeRestricted.subset {α : Type*} {D E : Domain α}
    (hD : ExtremeRestricted D) (hED : E ⊆ D) : ExtremeRestricted E := by
  intro a b c hab hac hbc
  obtain ⟨p,hp,H⟩ := hD a b c hab hac hbc
  refine ⟨p,hp,?_⟩
  rcases H with H | H | H
  · exact Or.inl (fun r hr => H r (hED hr))
  · exact Or.inr (Or.inl (fun r hr => H r (hED hr)))
  · exact Or.inr (Or.inr (fun r hr => H r (hED hr)))

theorem extremeFullDomain_isPeakPit {n : Nat} (L : ExtremeSelection n)
    (Q : FixedPairs n) : IsPeakPit (extremeFullDomain L Q) := by
  classical
  apply ExtremeRestricted.isPeakPit
  exact (extreme_full_isPeakPit L).2.subset (Finset.filter_subset _ _)

theorem IsExtremeFull.isPeakPit {n : Nat} {D : Domain (Fin n)}
    (H : IsExtremeFull D) : IsPeakPit D := by
  obtain ⟨L,Q,rfl⟩ := H
  exact extremeFullDomain_isPeakPit L Q

theorem ExtremeRestricted.choose_extreme_law {n : Nat} {D : Domain (Fin n)}
    (hD : ExtremeRestricted D) (t : Triple n) :
    ∃ law : Fin 3 × Fin 3, law.2 ≠ 1 ∧ ∀ r ∈ D, HoldsLaw r t law := by
  obtain ⟨p,hp,H⟩ := hD t.val.1 t.val.2.1 t.val.2.2 (ne_of_lt t.property.1)
    (ne_of_lt (lt_trans t.property.1 t.property.2)) (ne_of_lt t.property.2)
  rcases H with H | H | H
  · exact ⟨(0,p),hp,H⟩
  · exact ⟨(1,p),hp,H⟩
  · exact ⟨(2,p),hp,H⟩

theorem ExtremeRestricted.completion {n : Nat} {D : Domain (Fin n)}
    (hD : ExtremeRestricted D) : ∃ L : ExtremeSelection n, D ⊆ fullDomain L.val := by
  classical
  choose L hp hL using hD.choose_extreme_law
  refine ⟨⟨L,hp⟩,?_⟩
  intro r hr
  exact (mem_fullDomain L r).mpr (fun t => hL t r hr)

/-- A largest peak-pit domain is already full under some extreme selection.
This uses maximal SIZE among peak-pit domains, never maximality among all CDs. -/
theorem maximum_peakPit_isExtremeFull {n : Nat} {D : Domain (Fin n)}
    (hD : IsPeakPit D) (hcard : D.card = h n) :
    ∃ L : ExtremeSelection n, D = fullDomain L.val := by
  obtain ⟨L,hsub⟩ := hD.2.completion
  refine ⟨L,Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [hcard]
  exact card_le_h (extreme_full_isPeakPit L)

theorem fullDomain_extreme_isExtremeFull {n : Nat} (L : ExtremeSelection n) :
    IsExtremeFull (fullDomain L.val) := by
  classical
  refine ⟨L,fun _ => none,?_⟩
  ext r
  simp [extremeFullDomain, HoldsPairs]

theorem maximum_peakPit_fullClass {n : Nat} {D : Domain (Fin n)}
    (hD : IsPeakPit D) (hcard : D.card = h n) : IsExtremeFull D := by
  obtain ⟨L,rfl⟩ := maximum_peakPit_isExtremeFull hD hcard
  exact fullDomain_extreme_isExtremeFull L

#print axioms extremeFullDomain_isPeakPit
#print axioms ExtremeRestricted.completion
#print axioms maximum_peakPit_isExtremeFull
end Condorcet
