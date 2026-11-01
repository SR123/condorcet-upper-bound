import CDCert.Main
import CDCert.TwoInputs

namespace TutorialCorrespondence
open Condorcet Filter Topology

-- The tutorial's semantic definition, including repeated voters.
theorem condorcet_definition {α : Type*} (D : Domain α) :
    IsCondorcet D ↔ ∀ (m : Nat), Odd m → ∀ v : Fin m → Order α,
      (∀ i, v i ∈ D) → Transitive (majority v) := Iff.rfl

theorem peak_pit_definition {α : Type*} (D : Domain α) :
    IsPeakPit D ↔ IsCondorcet D ∧ ExtremeRestricted D := Iff.rfl

theorem triple_characterization {α : Type*} (D : Domain α) :
    IsCondorcet D ↔ ValueRestricted D := isCondorcet_iff_valueRestricted D

-- All seven Main conclusions, with the tutorial's literal hypotheses.
theorem general_recurrence {N : Nat} (hN : 3 ≤ N) :
    (11 * N + 8) * f N ≤ 32 * N * f (N - 1) := CDCert.Main.general_recurrence hN

theorem general_geometric {N : Nat} (hN : 3 ≤ N) :
    (f N : ℝ) ≤ 4 * (32 / 11 : ℝ) ^ (N - 3) := CDCert.Main.general_geometric hN

theorem peak_recurrence {N : Nat} (hN : 3 ≤ N) :
    3 * h N ≤ 8 * h (N - 1) := CDCert.Main.peak_recurrence hN

theorem peak_geometric {N : Nat} (hN : 3 ≤ N) :
    (h N : ℝ) ≤ 4 * (8 / 3 : ℝ) ^ (N - 3) := CDCert.Main.peak_geometric hN

theorem general_limit :
    ∃ L, Tendsto (fun N : Nat => (f N : ℝ) ^ ((1 : ℝ) / N)) atTop (𝓝 L) ∧ L ≤ 32 / 11 :=
  CDCert.Main.general_limit

theorem peak_limit :
    ∃ L, Tendsto (fun N : Nat => (h N : ℝ) ^ ((1 : ℝ) / N)) atTop (𝓝 L) ∧ L ≤ 8 / 3 :=
  CDCert.Main.peak_limit

theorem general_polynomial_correction :
    (fun N : Nat => (f N : ℝ)) =O[atTop]
      (fun N : Nat => (N : ℝ) ^ (-(8 / 11 : ℝ)) * (32 / 11 : ℝ) ^ N) :=
  CDCert.Main.general_polynomial_correction

-- The tutorial writes N alternatives; these statements set N=k+1.
theorem first_input {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsMaximal D) :
    gapCount D + (k + 2) * D.card ≤ 3 * deletionSum D := CDCert.TwoInputs.first_input hD

theorem second_input {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsFull D) :
    3 * (k + 1) * D.card ≤ 8 * (deletionSum D + gapCount D) := CDCert.TwoInputs.second_input hD

theorem transfer {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsMaximal D) :
    (11 * (k + 1) + 8) * D.card ≤ 32 * deletionSum D := CDCert.TwoInputs.transfer hD

-- These are the ten further entries in the independent 20-result audit.
theorem gap_inequality {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsMaximal D) :
    gapCount D + (k + 2) * D.card ≤ 3 * deletionSum D := CDCert.Recurrences.gap_inequality hD

theorem deletion_lower_bound {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsMaximal D) :
    (11 * (k + 1) + 8) * D.card ≤ 32 * deletionSum D := CDCert.Recurrences.deletion_lower_bound hD

theorem extreme_density {k : Nat} {D : Domain (Fin (k + 1))} (hD : InF D) :
    3 * (k + 1) * D.card ≤ 8 * deletionSum D := CDCert.Bridge.InF.density hD

theorem free_le_locked {k : Nat} {D : Domain (Fin (k + 1))} (hD : IsMaximal D) :
    freeCount D ≤ lockedCount D := CDCert.FreeLocked.free_le_locked hD

theorem finite_lemma {J : List Nat → Bool} (hJ : CDCert.K6.DomE 7 J) :
    (CDCert.K6.cD5 : Int) * CDCert.K6.cost10 J ≤ 11057646600 * CDCert.K6.card 7 J +
      ((List.range 7).map (fun z => CDCert.K6.qD (CDCert.K6.botP z J))).sum -
      ((List.range 7).map (fun w => CDCert.K6.qD (CDCert.K6.topP w J))).sum :=
  CDCert.K6.finite_lemma hJ

theorem adjacency_density {N : Nat} {K : List Nat → Bool} (hK : CDCert.K6.IsDom N K) :
    8 * CDCert.K6.adj N K ≤ 5 * N * CDCert.K6.card N K := CDCert.K6.adj_le hK

theorem general_supermultiplicativity (m n : Nat) : f m * f n ≤ f (m + n) :=
  CDCert.Supermult.f_supermul m n

theorem peak_supermultiplicativity (m n : Nat) : h m * h n ≤ h (m + n) :=
  CDCert.Supermult.h_supermul m n

theorem general_successor (k : Nat) :
    (11 * (k + 1) + 8) * f (k + 1) ≤ 32 * (k + 1) * f k :=
  CDCert.Recurrences.general_recurrence k

theorem peak_successor (k : Nat) : 3 * h (k + 1) ≤ 8 * h k :=
  CDCert.Bounds.peakPit_recurrence k

end TutorialCorrespondence

-- Original audited declarations, printed directly rather than inferred from comments.
#check @CDCert.Main.general_recurrence
#print axioms CDCert.Main.general_recurrence
#check @CDCert.Main.general_geometric
#print axioms CDCert.Main.general_geometric
#check @CDCert.Main.peak_recurrence
#print axioms CDCert.Main.peak_recurrence
#check @CDCert.Main.peak_geometric
#print axioms CDCert.Main.peak_geometric
#check @CDCert.Main.general_limit
#print axioms CDCert.Main.general_limit
#check @CDCert.Main.peak_limit
#print axioms CDCert.Main.peak_limit
#check @CDCert.Main.general_polynomial_correction
#print axioms CDCert.Main.general_polynomial_correction
#check @CDCert.TwoInputs.first_input
#print axioms CDCert.TwoInputs.first_input
#check @CDCert.TwoInputs.second_input
#print axioms CDCert.TwoInputs.second_input
#check @CDCert.TwoInputs.transfer
#print axioms CDCert.TwoInputs.transfer
#check @CDCert.Recurrences.gap_inequality
#print axioms CDCert.Recurrences.gap_inequality
#check @CDCert.Recurrences.deletion_lower_bound
#print axioms CDCert.Recurrences.deletion_lower_bound
#check @CDCert.Bridge.InF.density
#print axioms CDCert.Bridge.InF.density
#check @CDCert.FreeLocked.free_le_locked
#print axioms CDCert.FreeLocked.free_le_locked
#check @CDCert.K6.finite_lemma
#print axioms CDCert.K6.finite_lemma
#check @CDCert.K6.adj_le
#print axioms CDCert.K6.adj_le
#check @CDCert.Supermult.f_supermul
#print axioms CDCert.Supermult.f_supermul
#check @CDCert.Supermult.h_supermul
#print axioms CDCert.Supermult.h_supermul
#check @CDCert.Recurrences.general_recurrence
#print axioms CDCert.Recurrences.general_recurrence
#check @CDCert.Bounds.peakPit_recurrence
#print axioms CDCert.Bounds.peakPit_recurrence
#print Condorcet.Order
#print Condorcet.IsStrictTotal
#print Condorcet.majority
#print Condorcet.IsCondorcet
#print Condorcet.Never
#print Condorcet.ValueRestricted
#print Condorcet.ExtremeRestricted
#print Condorcet.IsPeakPit
#print Condorcet.f
#print Condorcet.h
#print Condorcet.IsMaximal
#print Condorcet.IsFull
#print Condorcet.IsExtremeFull
#print Condorcet.InF
#print CDCert.K6.IsDom
#print CDCert.K6.DomE
#print CDCert.K6.qD
#print CDCert.K6.cost10
#check @Condorcet.deletion_gap_adjacency_identity
#check @Condorcet.IsExtremeFull.gapCount_zero
#check @Condorcet.IsFull.component_inF
#check @Condorcet.IsFull.sum_components_deletionSum
#check @Condorcet.IsFull.median_mem
#check @Condorcet.IsFull.component_from_fixed
#check @Condorcet.IsFull.missing_swap
#check @Condorcet.IsFull.second_move_count
#check @Condorcet.IsFull.gap_slack_identity
#check @CDCert.Bridge.before_toList
#check @CDCert.Bridge.toList_injective
#check @CDCert.Bridge.InF.toList_domain
#check @CDCert.Bridge.card_adj_of_choice
#check @CDCert.Bridge.toList_swapLetter
#check @CDCert.K6.window_bound
#check @CDCert.K6.dbl_props
#check @CDCert.K6.seven_finite
#check @CDCert.K6.lamD_eq
#check @CDCert.K6.lam_receiver
#check @TutorialCorrespondence.condorcet_definition
#print axioms TutorialCorrespondence.condorcet_definition
#check @TutorialCorrespondence.peak_pit_definition
#print axioms TutorialCorrespondence.peak_pit_definition
#check @TutorialCorrespondence.triple_characterization
#print axioms TutorialCorrespondence.triple_characterization
#check @TutorialCorrespondence.general_recurrence
#print axioms TutorialCorrespondence.general_recurrence
#check @TutorialCorrespondence.general_geometric
#print axioms TutorialCorrespondence.general_geometric
#check @TutorialCorrespondence.peak_recurrence
#print axioms TutorialCorrespondence.peak_recurrence
#check @TutorialCorrespondence.peak_geometric
#print axioms TutorialCorrespondence.peak_geometric
#check @TutorialCorrespondence.general_limit
#print axioms TutorialCorrespondence.general_limit
#check @TutorialCorrespondence.peak_limit
#print axioms TutorialCorrespondence.peak_limit
#check @TutorialCorrespondence.general_polynomial_correction
#print axioms TutorialCorrespondence.general_polynomial_correction
#check @TutorialCorrespondence.first_input
#print axioms TutorialCorrespondence.first_input
#check @TutorialCorrespondence.second_input
#print axioms TutorialCorrespondence.second_input
#check @TutorialCorrespondence.transfer
#print axioms TutorialCorrespondence.transfer
#check @TutorialCorrespondence.gap_inequality
#print axioms TutorialCorrespondence.gap_inequality
#check @TutorialCorrespondence.deletion_lower_bound
#print axioms TutorialCorrespondence.deletion_lower_bound
#check @TutorialCorrespondence.extreme_density
#print axioms TutorialCorrespondence.extreme_density
#check @TutorialCorrespondence.free_le_locked
#print axioms TutorialCorrespondence.free_le_locked
#check @TutorialCorrespondence.finite_lemma
#print axioms TutorialCorrespondence.finite_lemma
#check @TutorialCorrespondence.adjacency_density
#print axioms TutorialCorrespondence.adjacency_density
#check @TutorialCorrespondence.general_supermultiplicativity
#print axioms TutorialCorrespondence.general_supermultiplicativity
#check @TutorialCorrespondence.peak_supermultiplicativity
#print axioms TutorialCorrespondence.peak_supermultiplicativity
#check @TutorialCorrespondence.general_successor
#print axioms TutorialCorrespondence.general_successor
#check @TutorialCorrespondence.peak_successor
#print axioms TutorialCorrespondence.peak_successor
