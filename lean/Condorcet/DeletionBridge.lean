import Condorcet.Runs
import Condorcet.Extremal
import Mathlib.Logic.Equiv.Fin.Basic

namespace Condorcet
namespace Order
variable {α β : Type*}

/-- Change alternative labels along an equivalence. -/
def transport (e : α ≃ β) (r : Order α) : Order β := restrict e.symm.toEmbedding r

@[simp] theorem transport_apply (e : α ≃ β) (r : Order α) (a b : β) :
    transport e r a b = r (e.symm a) (e.symm b) := rfl

@[simp] theorem transport_symm_transport (e : α ≃ β) (r : Order α) :
    transport e.symm (transport e r) = r := by
  ext a b
  simp

@[simp] theorem transport_transport_symm (e : α ≃ β) (r : Order β) :
    transport e (transport e.symm r) = r := by
  ext a b
  simp

theorem transport_injective (e : α ≃ β) : Function.Injective (transport e) := by
  intro r s h
  have := congrArg (transport e.symm) h
  simpa using this

end Order

noncomputable def transportDomain {α β : Type*} (e : α ≃ β) (D : Domain α) : Domain β :=
  D.image (Order.transport e)

@[simp] theorem card_transportDomain {α β : Type*} (e : α ≃ β) (D : Domain α) :
    (transportDomain e D).card = D.card := by
  classical
  exact Finset.card_image_of_injective _ (Order.transport_injective e)

/-- The distinguished deleted label corresponds to `none`; all others use succAbove. -/
def deletionEquiv {n : Nat} (x : Fin (n + 1)) : Option (Fin n) ≃ Fin (n + 1) :=
  (finSuccEquiv' x).symm

@[simp] theorem deletionEquiv_none {n : Nat} (x : Fin (n + 1)) :
    deletionEquiv x none = x := rfl

@[simp] theorem deletionEquiv_some {n : Nat} (x : Fin (n + 1)) (a : Fin n) :
    deletionEquiv x (some a) = x.succAbove a := rfl

/-- Actual order deletion agrees under the two label conventions. -/
theorem restrict_delete_transport {n : Nat} (x : Fin (n + 1))
    (r : Order (Option (Fin n))) :
    Order.restrict (deleteEmbedding x) (Order.transport (deletionEquiv x) r) =
      Order.restrict Order.someEmbedding r := by
  ext a b
  simp [deleteEmbedding, deletionEquiv, Order.someEmbedding]

theorem delete_transportDomain {n : Nat} (x : Fin (n + 1))
    (D : Domain (Option (Fin n))) :
    deleteDomain x (transportDomain (deletionEquiv x) D) =
      restrictDomain Order.someEmbedding D := by
  classical
  unfold deleteDomain transportDomain restrictDomain
  rw [Finset.image_image]
  apply Finset.image_congr
  intro r _
  exact restrict_delete_transport x r

/-- Pull an arbitrary labelled domain into the insertion-slot convention. -/
noncomputable def optionDomain {n : Nat} (x : Fin (n + 1)) (D : Domain (Fin (n + 1))) :
    Domain (Option (Fin n)) := transportDomain (deletionEquiv x).symm D

@[simp] theorem transport_optionDomain {n : Nat} (x : Fin (n + 1))
    (D : Domain (Fin (n + 1))) :
    transportDomain (deletionEquiv x) (optionDomain x D) = D := by
  classical
  unfold optionDomain transportDomain
  rw [Finset.image_image]
  have hf : (Order.transport (deletionEquiv x)) ∘
      (Order.transport (deletionEquiv x).symm) = id := by
    funext r
    ext a b
    simp
  rw [hf]
  exact Finset.image_id

theorem optionDomain_deletion {n : Nat} (x : Fin (n + 1)) (D : Domain (Fin (n + 1))) :
    restrictDomain Order.someEmbedding (optionDomain x D) = deleteDomain x D := by
  rw [← delete_transportDomain, transport_optionDomain]

/-- Total numbers of fibre gaps and occupied consecutive slot pairs.
Identification of the latter with directed adjacent swaps is a separate theorem. -/
noncomputable def gapCount {n : Nat} (D : Domain (Fin (n + 1))) : Nat :=
  ∑ x : Fin (n + 1), ∑ P ∈ deleteDomain x D,
    SlotWord.gaps (insertionWord (optionDomain x D) P)

noncomputable def slotAdjacencyCount {n : Nat} (D : Domain (Fin (n + 1))) : Nat :=
  ∑ x : Fin (n + 1), ∑ P ∈ deleteDomain x D,
    SlotWord.adjacentPairs (insertionWord (optionDomain x D) P)

/-- The global fibre-run identity for the actual deletion convention. -/
theorem global_fibre_run_identity {n : Nat} (D : Domain (Fin (n + 1))) :
    deletionSum D + gapCount D + slotAdjacencyCount D = (n + 1) * D.card := by
  classical
  have H : ∀ x : Fin (n + 1),
      (deleteDomain x D).card +
      (∑ P ∈ deleteDomain x D, SlotWord.gaps (insertionWord (optionDomain x D) P)) +
      (∑ P ∈ deleteDomain x D, SlotWord.adjacentPairs (insertionWord (optionDomain x D) P)) =
        D.card := by
    intro x
    have h := deletion_fibre_identity (optionDomain x D)
    rw [optionDomain_deletion] at h
    simpa [optionDomain] using h
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun x _ => H x)
  simpa [deletionSum, gapCount, slotAdjacencyCount, Finset.sum_add_distrib] using hsum

#print axioms restrict_delete_transport
#print axioms optionDomain_deletion
#print axioms global_fibre_run_identity
end Condorcet
