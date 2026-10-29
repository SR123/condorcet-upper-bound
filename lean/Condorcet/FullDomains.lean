import Condorcet.Adjacency

namespace Condorcet
open CondorcetUpperBounds

def CommonLaw {α : Type*} (D : Domain α) (a b c : α) : Prop :=
  ∃ p : Fin 3, (∀ r ∈ D, Never r a b c p) ∨
    (∀ r ∈ D, Never r b a c p) ∨ (∀ r ∈ D, Never r c a b p)

theorem CommonLaw.swap12 {α : Type*} {D : Domain α} {a b c : α}
    (H : CommonLaw D a b c) : CommonLaw D b a c := by
  obtain ⟨p,H⟩ := H
  refine ⟨p, ?_⟩
  rcases H with H | H | H
  · exact Or.inr (Or.inl H)
  · exact Or.inl H
  · exact Or.inr (Or.inr (fun r hr => (Never.swap r c a b p).mp (H r hr)))

theorem CommonLaw.swap23 {α : Type*} {D : Domain α} {a b c : α}
    (H : CommonLaw D a b c) : CommonLaw D a c b := by
  obtain ⟨p,H⟩ := H
  refine ⟨p, ?_⟩
  rcases H with H | H | H
  · exact Or.inl (fun r hr => (Never.swap r a b c p).mp (H r hr))
  · exact Or.inr (Or.inr H)
  · exact Or.inr (Or.inl H)

/-- Each unordered triple has exactly one increasing representative. -/
def Triple (n : Nat) := {t : Fin n × Fin n × Fin n // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

noncomputable instance (n : Nat) : Fintype (Triple n) := by
  classical
  unfold Triple
  infer_instance

abbrev Selection (n : Nat) := Triple n → Fin 3 × Fin 3

def HoldsLaw {n : Nat} (r : Order (Fin n)) (t : Triple n) (law : Fin 3 × Fin 3) : Prop :=
  if law.1 = 0 then Never r t.val.1 t.val.2.1 t.val.2.2 law.2
  else if law.1 = 1 then Never r t.val.2.1 t.val.1 t.val.2.2 law.2
  else Never r t.val.2.2 t.val.1 t.val.2.1 law.2

noncomputable def fullDomain {n : Nat} (L : Selection n) : Domain (Fin n) := by
  classical
  exact Finset.univ.filter (fun r => ∀ t, HoldsLaw r t (L t))

@[simp] theorem mem_fullDomain {n : Nat} (L : Selection n) (r : Order (Fin n)) :
    r ∈ fullDomain L ↔ ∀ t, HoldsLaw r t (L t) := by
  classical
  simp [fullDomain]

def IsFull {n : Nat} (D : Domain (Fin n)) : Prop := ∃ L : Selection n, D = fullDomain L

theorem sorted_common_implies_valueRestricted {n : Nat} {D : Domain (Fin n)}
    (H : ∀ a b c : Fin n, a < b → b < c → CommonLaw D a b c) : ValueRestricted D := by
  intro a b c hab hac hbc
  change CommonLaw D a b c
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

theorem fullDomain_isCondorcet {n : Nat} (L : Selection n) : IsCondorcet (fullDomain L) := by
  apply ValueRestricted.isCondorcet
  apply sorted_common_implies_valueRestricted
  intro a b c hab hbc
  let t : Triple n := ⟨(a,b,c), hab, hbc⟩
  have H : ∀ r ∈ fullDomain L, HoldsLaw r t (L t) := fun r hr => (mem_fullDomain L r).mp hr t
  rcases hEq : L t with ⟨x,p⟩
  rw [hEq] at H
  refine ⟨p, ?_⟩
  fin_cases x
  · exact Or.inl H
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr H)

theorem IsFull.isCondorcet {n : Nat} {D : Domain (Fin n)} (hD : IsFull D) : IsCondorcet D := by
  obtain ⟨L,rfl⟩ := hD
  exact fullDomain_isCondorcet L

theorem ValueRestricted.choose_law {n : Nat} {D : Domain (Fin n)} (hD : ValueRestricted D)
    (t : Triple n) : ∃ law : Fin 3 × Fin 3, ∀ r ∈ D, HoldsLaw r t law := by
  obtain ⟨p,H⟩ := hD t.val.1 t.val.2.1 t.val.2.2 (ne_of_lt t.property.1)
    (ne_of_lt (lt_trans t.property.1 t.property.2)) (ne_of_lt t.property.2)
  rcases H with H | H | H
  · exact ⟨(0,p),H⟩
  · exact ⟨(1,p),H⟩
  · exact ⟨(2,p),H⟩

theorem IsMaximal.isFull {n : Nat} {D : Domain (Fin n)} (hD : IsMaximal D) : IsFull D := by
  classical
  choose L hL using hD.1.valueRestricted.choose_law
  have hsub : D ⊆ fullDomain L := by
    intro r hr
    exact (mem_fullDomain L r).mpr (fun t => hL t r hr)
  exact ⟨L, (hD.2 _ (fullDomain_isCondorcet L) hsub).symm⟩

theorem IsFull.median_mem {n : Nat} {D : Domain (Fin n)} (hD : IsFull D)
    (u v w : Order (Fin n)) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) :
    medianOrder hD.isCondorcet u v w hu hv hw ∈ D := by
  obtain ⟨L,rfl⟩ := hD
  apply (mem_fullDomain L _).mpr
  intro t
  have h₁ := (mem_fullDomain L u).mp hu t
  have h₂ := (mem_fullDomain L v).mp hv t
  have h₃ := (mem_fullDomain L w).mp hw t
  rcases hEq : L t with ⟨x,p⟩
  rw [hEq] at h₁ h₂ h₃
  fin_cases x
  · exact Never.medianOrder _ u v w hu hv hw _ _ _ p h₁ h₂ h₃
  · exact Never.medianOrder _ u v w hu hv hw _ _ _ p h₁ h₂ h₃
  · exact Never.medianOrder _ u v w hu hv hw _ _ _ p h₁ h₂ h₃

theorem IsFull.encoded_medianClosed {n : Nat} {D : Domain (Fin n)}
    (hD : IsFull D) : MedianClosed (encodedDomain D) := by
  intro u v w hu hv hw
  obtain ⟨r, hr, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨medianOrder hD.isCondorcet r s t hr hs ht, hD.median_mem r s t hr hs ht, rfl⟩

theorem IsFull.component_from_fixed {n : Nat} {D : Domain (Fin n)}
    (hD : IsFull D) (r s : Order (Fin n)) (hr : r ∈ D) (hs : s ∈ D)
    (hfixed : ∀ i : Pair n,
      (∀ q ∈ D, Connected D r q → encode q i = encode r i) → encode s i = encode r i) :
    Connected D r s := by
  classical
  apply component_from_fixed_coordinates (encodedDomain D) hD.encoded_medianClosed
    (encode r) (encode s) ⟨r,hr,rfl⟩ ⟨s,hs,rfl⟩ (Finset.univ.toList) (by simp)
  intro i H
  exact hfixed i (fun q _ hq => H (encode q) hq)

#print axioms fullDomain_isCondorcet
#print axioms IsMaximal.isFull
#print axioms IsFull.median_mem
#print axioms IsFull.component_from_fixed
end Condorcet
