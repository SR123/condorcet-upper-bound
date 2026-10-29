import Condorcet.Fibres
import Mathlib.Algebra.BigOperators.Fin

namespace Condorcet
namespace SlotWord

/-- Number of occupied slots in a finite Boolean slot word. -/
def occupied : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + occupied bs

/-- A run starts at an occupied slot whose predecessor is unoccupied. -/
def starts (prev : Bool) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b && !prev then 1 else 0) + starts b bs

/-- Neighbouring occupied pairs, including the predecessor when it is true. -/
def edges (prev : Bool) : List Bool → Nat
  | [] => 0
  | b :: bs => (if prev && b then 1 else 0) + edges b bs

def runs (bs : List Bool) : Nat := starts false bs
def adjacentPairs (bs : List Bool) : Nat := edges false bs
def gaps (bs : List Bool) : Nat := runs bs - 1

theorem occupied_eq_starts_add_edges (bs : List Bool) (prev : Bool) :
    occupied bs = starts prev bs + edges prev bs := by
  induction bs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
    have H := ih b
    cases prev <;> cases b <;> simp_all [occupied, starts, edges] <;> omega

/-- The exact run identity for a finite insertion fibre. -/
theorem occupied_eq_runs_add_adjacentPairs (bs : List Bool) :
    occupied bs = runs bs + adjacentPairs bs := occupied_eq_starts_add_edges bs false

theorem runs_pos (bs : List Bool) (h : 0 < occupied bs) : 0 < runs bs := by
  induction bs with
  | nil => simp [occupied] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have hh : 0 < occupied bs := by simpa [occupied] using h
      simpa [runs, starts] using ih hh
    | true => simp [runs, starts]

theorem gaps_add_one (bs : List Bool) (h : 0 < occupied bs) : gaps bs + 1 = runs bs := by
  have H := runs_pos bs h
  unfold gaps
  omega

theorem nonempty_run_identity (bs : List Bool) (h : 0 < occupied bs) :
    occupied bs = adjacentPairs bs + gaps bs + 1 := by
  have H := occupied_eq_runs_add_adjacentPairs bs
  have G := gaps_add_one bs h
  omega

theorem occupied_eq_sum (bs : List Bool) : occupied bs = (bs.map Bool.toNat).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [occupied, ih]

#print axioms occupied_eq_runs_add_adjacentPairs
#print axioms nonempty_run_identity
end SlotWord

variable {α : Type*} [Fintype α]

/-- Occupied insertion slots in their actual increasing slot order. -/
noncomputable def insertionWord (D : Domain (Option α)) (P : Order α) : List Bool := by
  classical
  exact List.ofFn (fun t : Fin (Fintype.card α + 1) => decide (t ∈ insertionSlots D P))

theorem occupied_insertionWord (D : Domain (Option α)) (P : Order α) :
    SlotWord.occupied (insertionWord D P) = (insertionSlots D P).card := by
  classical
  rw [SlotWord.occupied_eq_sum]
  simp only [insertionWord, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have hb : ∀ t : Fin (Fintype.card α + 1),
      (decide (t ∈ insertionSlots D P)).toNat = if t ∈ insertionSlots D P then 1 else 0 := by
    intro t
    by_cases ht : t ∈ insertionSlots D P <;> simp [ht]
  simp_rw [hb]
  simp [insertionSlots]

theorem actual_fibre_run_identity (D : Domain (Option α)) (P : Order α)
    (hP : P ∈ restrictDomain Order.someEmbedding D) :
    (insertionSlots D P).card = SlotWord.adjacentPairs (insertionWord D P) +
      SlotWord.gaps (insertionWord D P) + 1 := by
  have hpos : 0 < SlotWord.occupied (insertionWord D P) := by
    rw [occupied_insertionWord]
    exact Finset.card_pos.mpr ((insertionSlots_nonempty D P).mpr hP)
  have H := SlotWord.nonempty_run_identity (insertionWord D P) hpos
  rwa [occupied_insertionWord] at H

/-- Exact run count summed over the actual fibres of a deleted alternative.
The remaining global step identifies these slot adjacencies with all directed swaps. -/
theorem deletion_fibre_identity (D : Domain (Option α)) :
    (restrictDomain Order.someEmbedding D).card +
      (∑ P ∈ restrictDomain Order.someEmbedding D, SlotWord.gaps (insertionWord D P)) +
      (∑ P ∈ restrictDomain Order.someEmbedding D, SlotWord.adjacentPairs (insertionWord D P)) = D.card := by
  classical
  have H := sum_card_insertionSlots D
  have heq : (∑ P ∈ restrictDomain Order.someEmbedding D, (insertionSlots D P).card) =
      ∑ P ∈ restrictDomain Order.someEmbedding D,
        (SlotWord.adjacentPairs (insertionWord D P) + SlotWord.gaps (insertionWord D P) + 1) := by
    apply Finset.sum_congr rfl
    intro P hP
    exact actual_fibre_run_identity D P hP
  rw [heq] at H
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at H
  omega

#print axioms actual_fibre_run_identity
#print axioms deletion_fibre_identity
end Condorcet
