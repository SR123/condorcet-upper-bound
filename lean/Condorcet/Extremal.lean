import Condorcet.Orders
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Condorcet

/-- Maximum over actual semantic Condorcet domains on n labelled alternatives. -/
noncomputable def f (n : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Domain (Fin n))).filter IsCondorcet).sup Finset.card

/-- Maximum over actual peak-pit Condorcet domains on n alternatives. -/
noncomputable def h (n : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Domain (Fin n))).filter IsPeakPit).sup Finset.card

theorem card_le_f {n : Nat} {D : Domain (Fin n)} (hD : IsCondorcet D) : D.card ≤ f n := by
  classical
  exact Finset.le_sup (by simp [hD])

theorem card_le_h {n : Nat} {D : Domain (Fin n)} (hD : IsPeakPit D) : D.card ≤ h n := by
  classical
  exact Finset.le_sup (by simp [hD])

theorem h_le_f (n : Nat) : h n ≤ f n := by
  classical
  apply Finset.sup_le
  intro D hD
  exact card_le_f ((Finset.mem_filter.mp hD).2.1)

/-- Canonical injection identifying all labels except x with Fin n. -/
def deleteEmbedding {n : Nat} (x : Fin (n + 1)) : Fin n ↪ Fin (n + 1) :=
  ⟨x.succAbove, x.succAbove_right_injective⟩

noncomputable def deleteDomain {n : Nat} (x : Fin (n + 1)) (D : Domain (Fin (n + 1))) :
    Domain (Fin n) := restrictDomain (deleteEmbedding x) D

noncomputable def deletionSum {n : Nat} (D : Domain (Fin (n + 1))) : Nat :=
  ∑ x : Fin (n + 1), (deleteDomain x D).card

/-- The actual deletion estimate, discharged from the definitions. -/
theorem deletionSum_le_general {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsCondorcet D) : deletionSum D ≤ (n + 1) * f n := by
  classical
  unfold deletionSum
  calc
    ∑ x : Fin (n + 1), (deleteDomain x D).card ≤ ∑ _x : Fin (n + 1), f n := by
      apply Finset.sum_le_sum
      intro x _
      exact card_le_f (hD.restrict (deleteEmbedding x))
    _ = (n + 1) * f n := by simp

/-- The same estimate for the peak-pit extremum. -/
theorem deletionSum_le_peakPit {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsPeakPit D) : deletionSum D ≤ (n + 1) * h n := by
  classical
  unfold deletionSum
  calc
    ∑ x : Fin (n + 1), (deleteDomain x D).card ≤ ∑ _x : Fin (n + 1), h n := by
      apply Finset.sum_le_sum
      intro x _
      exact card_le_h (hD.restrict (deleteEmbedding x))
    _ = (n + 1) * h n := by simp

/-- An empty domain has no nonempty odd voter profile. -/
theorem empty_isCondorcet {α : Type*} : IsCondorcet (∅ : Domain α) := by
  intro m hm v hv
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => by subst m; simpa using hm)
  have hi := hv ⟨0, hmpos⟩
  simp at hi

theorem empty_isPeakPit {α : Type*} : IsPeakPit (∅ : Domain α) := by
  refine ⟨empty_isCondorcet, ?_⟩
  intro a b c _ _ _
  refine ⟨0, by decide, Or.inl ?_⟩
  simp

theorem exists_maximum_general (n : Nat) :
    ∃ D : Domain (Fin n), IsCondorcet D ∧ D.card = f n := by
  classical
  let domains := (Finset.univ : Finset (Domain (Fin n))).filter IsCondorcet
  have hn : domains.Nonempty := ⟨∅, by simp [domains, empty_isCondorcet]⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_mem_eq_sup domains hn Finset.card
  exact ⟨D, (Finset.mem_filter.mp hD).2, hmax.symm⟩

theorem exists_maximum_peakPit (n : Nat) :
    ∃ D : Domain (Fin n), IsPeakPit D ∧ D.card = h n := by
  classical
  let domains := (Finset.univ : Finset (Domain (Fin n))).filter IsPeakPit
  have hn : domains.Nonempty := ⟨∅, by simp [domains, empty_isPeakPit]⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_mem_eq_sup domains hn Finset.card
  exact ⟨D, (Finset.mem_filter.mp hD).2, hmax.symm⟩

def IsMaximal {α : Type*} (D : Domain α) : Prop :=
  IsCondorcet D ∧ ∀ E : Domain α, IsCondorcet E → D ⊆ E → E = D

theorem maximum_isMaximal {n : Nat} {D : Domain (Fin n)}
    (hD : IsCondorcet D) (hcard : D.card = f n) : IsMaximal D := by
  refine ⟨hD, ?_⟩
  intro E hE hDE
  apply Eq.symm
  exact Finset.eq_of_subset_of_card_le hDE (hcard ▸ card_le_f hE)

#print axioms IsCondorcet.restrict
#print axioms deletionSum_le_general
#print axioms deletionSum_le_peakPit
#print axioms exists_maximum_general
#print axioms maximum_isMaximal

end Condorcet
