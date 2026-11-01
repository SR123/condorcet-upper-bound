import CDCert.Main
import CDCert.TwoInputs

/-! Literal restatements of the tutorial's other mathematical interfaces.
The original 23 restatements are in TutorialCorrespondence.lean.
These declarations add no assumptions and do not modify the original project.
-/
namespace TutorialSupportStatements
open Condorcet CondorcetUpperBounds
open scoped BigOperators

theorem strict_order_definition {α : Type*} (r : α → α → Bool) :
    IsStrictTotal r ↔
      (∀ a, r a a = false) ∧
      (∀ a b c, r a b = true → r b c = true → r a c = true) ∧
      (∀ a b, a ≠ b → r a b = true ∨ r b a = true) := Iff.rfl

theorem maximum_general_is_maximal {n : Nat} {D : Domain (Fin n)}
    (hD : IsCondorcet D) (hcard : D.card = f n) : IsMaximal D :=
  maximum_isMaximal hD hcard

theorem maximal_is_full {n : Nat} {D : Domain (Fin n)} (hD : IsMaximal D) : IsFull D :=
  hD.isFull

theorem maximum_peak_completion {n : Nat} {D : Domain (Fin n)}
    (hD : IsPeakPit D) (hcard : D.card = h n) :
    ∃ L : ExtremeSelection n, D = fullDomain L.val :=
  maximum_peakPit_isExtremeFull hD hcard

theorem maximum_peak_full_class {n : Nat} {D : Domain (Fin n)}
    (hD : IsPeakPit D) (hcard : D.card = h n) : IsExtremeFull D :=
  maximum_peakPit_fullClass hD hcard

theorem maximum_peak_inF {n : Nat} {D : Domain (Fin n)}
    (hD : IsPeakPit D) (hcard : D.card = h n) : InF D := by
  refine ⟨Finset.card_pos.mp ?_, maximum_peakPit_fullClass hD hcard⟩
  rw [hcard]
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (CDCert.Supermult.one_le_h n)

theorem general_deletion_upper {k : Nat} {D : Domain (Fin (k+1))} (hD : IsCondorcet D) :
    deletionSum D ≤ (k+1) * f k := deletionSum_le_general hD

theorem peak_deletion_upper {k : Nat} {D : Domain (Fin (k+1))} (hD : IsPeakPit D) :
    deletionSum D ≤ (k+1) * h k := deletionSum_le_peakPit hD

theorem fibre_identity {k : Nat} (D : Domain (Fin (k+1))) :
    deletionSum D + gapCount D + adjacencyCount D = (k+1) * D.card :=
  deletion_gap_adjacency_identity D

theorem interval_fibres {k : Nat} {D : Domain (Fin (k+1))} (hD : IsExtremeFull D)
    (x : Fin (k+1)) (P : Order (Fin k)) :
    SlotWord.Interval (insertionWord (optionDomain x D) P) := hD.insertionWord_interval x P

theorem no_gaps {k : Nat} {D : Domain (Fin (k+1))} (hD : IsExtremeFull D) :
    gapCount D = 0 := hD.gapCount_zero

theorem interval_deletion_count {k : Nat} {D : Domain (Fin (k+1))} (hD : IsExtremeFull D) :
    deletionSum D + adjacencyCount D = (k+1) * D.card := by
  simpa [hD.gapCount_zero] using deletion_gap_adjacency_identity D

theorem first_move_count {k : Nat} (D : Domain (Fin (k+1))) :
    2 * deletionSum D + freeCount D = (k+1) * D.card + frozenCount D :=
  Condorcet.first_move_count D

theorem second_move_count {k : Nat} {D : Domain (Fin (k+1))} (hD : IsFull D) :
    2 * deletionSum D + adjacencyCount D = (k+2) * D.card + lockedCount D :=
  hD.second_move_count

theorem gap_slack_count {k : Nat} {D : Domain (Fin (k+1))} (hD : IsFull D) :
    3 * deletionSum D + freeCount D =
      (k+2) * D.card + gapCount D + frozenCount D + lockedCount D := hD.gap_slack_identity

theorem fixed_pair_not_consecutive {k : Nat} {D : Domain (Fin (k+1))}
    (hD : IsMaximal D) (r : Order (Fin (k+1))) (p q : Fin (k+1))
    (hpq : p ≠ q) (hr : r ∈ D) (hfixed : ∀ u ∈ D, u p q = true) :
    ¬(∀ c, ¬(r p c = true ∧ r c q = true)) :=
  hD.fixed_pair_not_consecutive r p q hpq hr hfixed

theorem majority_closure {n : Nat} {D : Domain (Fin n)} (hD : IsFull D)
    (u v w : Order (Fin n)) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) :
    medianOrder hD.isCondorcet u v w hu hv hw ∈ D := hD.median_mem u v w hu hv hw

theorem component_from_fixed {n : Nat} {D : Domain (Fin n)}
    (hD : IsFull D) (r s : Order (Fin n)) (hr : r ∈ D) (hs : s ∈ D)
    (hfixed : ∀ i : Pair n,
      (∀ q ∈ D, Connected D r q → encode q i = encode r i) → encode s i = encode r i) :
    Connected D r s := hD.component_from_fixed r s hr hs hfixed

theorem component_extreme_full {n : Nat} {D : Domain (Fin n)} (hD : IsFull D)
    (r : Order (Fin n)) (hr : r ∈ D) : InF (component D r) := hD.component_inF r hr

theorem component_deletion_count {k : Nat} {D : Domain (Fin (k+1))} (hD : IsFull D) :
    ∑ K ∈ components D, deletionSum K = deletionSum D + gapCount D :=
  hD.sum_components_deletionSum

theorem component_cardinality {n : Nat} (D : Domain (Fin n)) :
    ∑ K ∈ components D, K.card = D.card := sum_components_card D

theorem component_membership {n : Nat} {D : Domain (Fin n)} (hD : IsFull D)
    (r s : Order (Fin n)) (hr : r ∈ D) :
    s ∈ component D r ↔ s ∈ D ∧ HoldsPairs (componentPairs D r) s :=
  Condorcet.component_membership hD r s hr

theorem window_estimate {n : Nat} {K : List Nat → Bool} (hK : CDCert.K6.DomE n K)
    (hn : 7 ≤ n) :
    8 * 8846117280 * (CDCert.K6.adj n K : Int) ≤
      5 * 8846117280 * ((n : Int) * CDCert.K6.card n K) +
      (10 * 8846117280 + 2 ^ 66) * CDCert.K6.card n K := CDCert.K6.window_bound hK hn

theorem copy_cardinality (n n' : Nat) (K K' : List Nat → Bool) :
    CDCert.K6.card (n+n') (CDCert.K6.concat n K K') =
      CDCert.K6.card n K * CDCert.K6.card n' K' := CDCert.K6.card_concat n n' K K'

theorem copies_preserve_class {n n' : Nat} {K K' : List Nat → Bool}
    (hK : CDCert.K6.IsDom n K) (hK' : CDCert.K6.IsDom n' K') :
    CDCert.K6.IsDom (n+n') (CDCert.K6.concat n K K') := CDCert.K6.isDom_concat hK hK'

theorem copy_adjacency (n n' : Nat) (K K' : List Nat → Bool) (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    CDCert.K6.adj (n+n') (CDCert.K6.concat n K K') =
      CDCert.K6.adj n K * CDCert.K6.card n' K' + CDCert.K6.card n K * CDCert.K6.adj n' K' :=
  CDCert.K6.adj_concat n n' K K' hn hn'

theorem no_join_swap (n n' : Nat) (K K' : List Nat → Bool) (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    CDCert.K6.adjAt (n+n') (n-1) (CDCert.K6.concat n K K') = 0 :=
  CDCert.K6.adjAt_concat_mid n n' K K' hn hn'

theorem copies_power_two {n : Nat} {K : List Nat → Bool} (hK : CDCert.K6.IsDom n K)
    (hn : 1 ≤ n) : ∀ k,
    CDCert.K6.IsDom (2^k*n) (CDCert.K6.dbl n K k) ∧
    CDCert.K6.card (2^k*n) (CDCert.K6.dbl n K k) = CDCert.K6.card n K ^ (2^k) ∧
    CDCert.K6.adj (2^k*n) (CDCert.K6.dbl n K k) * CDCert.K6.card n K =
      2^k * CDCert.K6.adj n K * CDCert.K6.card n K ^ (2^k) := CDCert.K6.dbl_props hK hn

theorem base_general : f 3 = 4 := f_three
theorem base_peak : h 3 = 4 := h_three

-- The rational form of the finite theorem: C=cost10/10 and q=qD/(2d).
theorem finite_rational {J : List Nat → Bool} (hJ : CDCert.K6.DomE 7 J) :
    (CDCert.K6.cost10 J : ℚ) / 10 ≤
      (5/8 : ℚ) * CDCert.K6.card 7 J +
      (((List.range 7).map (fun z => CDCert.K6.qD (CDCert.K6.botP z J))).sum : Int) /
        (2 * 8846117280 : ℚ) -
      (((List.range 7).map (fun w => CDCert.K6.qD (CDCert.K6.topP w J))).sum : Int) /
        (2 * 8846117280 : ℚ) := by
  have h := CDCert.K6.finite_lemma hJ
  norm_num [CDCert.K6.cD5] at h
  have hq : (1769223456 : ℚ) * CDCert.K6.cost10 J ≤
      11057646600 * CDCert.K6.card 7 J +
      (((List.range 7).map (fun z => CDCert.K6.qD (CDCert.K6.botP z J))).sum : Int) -
      (((List.range 7).map (fun w => CDCert.K6.qD (CDCert.K6.topP w J))).sum : Int) := by
    exact_mod_cast h
  linarith

end TutorialSupportStatements

#check @TutorialSupportStatements.strict_order_definition
#print axioms TutorialSupportStatements.strict_order_definition
#check @TutorialSupportStatements.maximum_general_is_maximal
#print axioms TutorialSupportStatements.maximum_general_is_maximal
#check @TutorialSupportStatements.maximal_is_full
#print axioms TutorialSupportStatements.maximal_is_full
#check @TutorialSupportStatements.maximum_peak_completion
#print axioms TutorialSupportStatements.maximum_peak_completion
#check @TutorialSupportStatements.maximum_peak_full_class
#print axioms TutorialSupportStatements.maximum_peak_full_class
#check @TutorialSupportStatements.maximum_peak_inF
#print axioms TutorialSupportStatements.maximum_peak_inF
#check @TutorialSupportStatements.general_deletion_upper
#print axioms TutorialSupportStatements.general_deletion_upper
#check @TutorialSupportStatements.peak_deletion_upper
#print axioms TutorialSupportStatements.peak_deletion_upper
#check @TutorialSupportStatements.fibre_identity
#print axioms TutorialSupportStatements.fibre_identity
#check @TutorialSupportStatements.interval_fibres
#print axioms TutorialSupportStatements.interval_fibres
#check @TutorialSupportStatements.no_gaps
#print axioms TutorialSupportStatements.no_gaps
#check @TutorialSupportStatements.interval_deletion_count
#print axioms TutorialSupportStatements.interval_deletion_count
#check @TutorialSupportStatements.first_move_count
#print axioms TutorialSupportStatements.first_move_count
#check @TutorialSupportStatements.second_move_count
#print axioms TutorialSupportStatements.second_move_count
#check @TutorialSupportStatements.gap_slack_count
#print axioms TutorialSupportStatements.gap_slack_count
#check @TutorialSupportStatements.fixed_pair_not_consecutive
#print axioms TutorialSupportStatements.fixed_pair_not_consecutive
#check @TutorialSupportStatements.majority_closure
#print axioms TutorialSupportStatements.majority_closure
#check @TutorialSupportStatements.component_from_fixed
#print axioms TutorialSupportStatements.component_from_fixed
#check @TutorialSupportStatements.component_extreme_full
#print axioms TutorialSupportStatements.component_extreme_full
#check @TutorialSupportStatements.component_deletion_count
#print axioms TutorialSupportStatements.component_deletion_count
#check @TutorialSupportStatements.component_cardinality
#print axioms TutorialSupportStatements.component_cardinality
#check @TutorialSupportStatements.component_membership
#print axioms TutorialSupportStatements.component_membership
#check @TutorialSupportStatements.window_estimate
#print axioms TutorialSupportStatements.window_estimate
#check @TutorialSupportStatements.copy_cardinality
#print axioms TutorialSupportStatements.copy_cardinality
#check @TutorialSupportStatements.copies_preserve_class
#print axioms TutorialSupportStatements.copies_preserve_class
#check @TutorialSupportStatements.copy_adjacency
#print axioms TutorialSupportStatements.copy_adjacency
#check @TutorialSupportStatements.no_join_swap
#print axioms TutorialSupportStatements.no_join_swap
#check @TutorialSupportStatements.copies_power_two
#print axioms TutorialSupportStatements.copies_power_two
#check @TutorialSupportStatements.base_general
#print axioms TutorialSupportStatements.base_general
#check @TutorialSupportStatements.base_peak
#print axioms TutorialSupportStatements.base_peak
#check @TutorialSupportStatements.finite_rational
#print axioms TutorialSupportStatements.finite_rational
