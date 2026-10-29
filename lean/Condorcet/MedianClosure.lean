import Condorcet.TripleCharacterization
import Condorcet.Extremal
import ComponentMedian

namespace Condorcet
open CondorcetUpperBounds

theorem Never.medianOrder {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    (u v w : Order α) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (x y z : α) (p : Fin 3)
    (h₁ : Never u x y z p) (h₂ : Never v x y z p) (h₃ : Never w x y z p) :
    Never (medianOrder hD u v w hu hv hw) x y z p := by
  fin_cases p
  · exact median_preserves_never_first _ _ _ _ _ _ h₁ h₂ h₃
  · exact median_preserves_never_middle _ _ _ _ _ _ h₁ h₂ h₃
  · exact median_preserves_never_last _ _ _ _ _ _ h₁ h₂ h₃

theorem IsCondorcet.insert_median {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    (u v w : Order α) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) :
    IsCondorcet (insert (medianOrder hD u v w hu hv hw) D) := by
  classical
  apply ValueRestricted.isCondorcet
  intro a b c hab hac hbc
  obtain ⟨p, hp⟩ := hD.valueRestricted a b c hab hac hbc
  have lift : ∀ x y z, (∀ r ∈ D, Never r x y z p) →
      ∀ r ∈ insert (medianOrder hD u v w hu hv hw) D, Never r x y z p := by
    intro x y z H r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Never.medianOrder hD u v w hu hv hw x y z p (H u hu) (H v hv) (H w hw)
    · exact H r hr
  refine ⟨p, ?_⟩
  rcases hp with hp | hp | hp
  · exact Or.inl (lift a b c hp)
  · exact Or.inr (Or.inl (lift b a c hp))
  · exact Or.inr (Or.inr (lift c a b hp))

/-- A maximal actual semantic domain contains the majority of any three members. -/
theorem IsMaximal.median_mem {α : Type*} {D : Domain α} (hD : IsMaximal D)
    (u v w : Order α) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) :
    medianOrder hD.1 u v w hu hv hw ∈ D := by
  classical
  have hIns := hD.1.insert_median u v w hu hv hw
  have heq := hD.2 _ hIns (Finset.subset_insert _ _)
  have hm := Finset.mem_insert_self (medianOrder hD.1 u v w hu hv hw) D
  rwa [heq] at hm

def encodedDomain {n : Nat} (D : Domain (Fin n)) (v : Pair n → Bool) : Prop :=
  ∃ r ∈ D, encode r = v

/-- The abstract component module's median-closure premise is now discharged
for actual maximal Condorcet domains with canonical unordered-pair coordinates. -/
theorem IsMaximal.encoded_medianClosed {n : Nat} {D : Domain (Fin n)}
    (hD : IsMaximal D) : MedianClosed (encodedDomain D) := by
  intro u v w hu hv hw
  obtain ⟨r, hr, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨medianOrder hD.1 r s t hr hs ht, hD.median_mem r s t hr hs ht, rfl⟩

#print axioms IsCondorcet.insert_median
#print axioms IsMaximal.median_mem
#print axioms IsMaximal.encoded_medianClosed
end Condorcet
