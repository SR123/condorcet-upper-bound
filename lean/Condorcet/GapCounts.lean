import Condorcet.Letters

namespace Condorcet
attribute [local instance] Classical.propDecidable

namespace Order

theorem rank_swapLabels {n : Nat} (r : Order (Fin (n+1))) (p q a : Fin (n+1)) :
    (r.swapLabels p q).rank a = r.rank (Equiv.swap p q a) := by
  classical
  have H : r.swapLabels p q = Order.transport (Equiv.swap p q).symm r := by
    ext u v
    simp [swapLabels_apply,transport_apply]
  rw [H,rank_transport]
  rfl

theorem Consecutive.deleted_upper {n : Nat} {r : Order (Fin (n+1))} {p q : Fin (n+1)}
    (h : r.Consecutive p q) : deletedOrder p (r.swapLabels p q) = deletedOrder p r := by
  ext a b
  apply (h.swap_agree (p.succAbove a) (p.succAbove b) ?_ ?_).symm
  · intro H
    exact Fin.succAbove_ne p a (congrArg Prod.fst H)
  · intro H
    exact Fin.succAbove_ne p b (congrArg Prod.snd H)

theorem Consecutive.deleted_lower {n : Nat} {r : Order (Fin (n+1))} {p q : Fin (n+1)}
    (h : r.Consecutive p q) : deletedOrder q (r.swapLabels p q) = deletedOrder q r := by
  ext a b
  apply (h.swap_agree (q.succAbove a) (q.succAbove b) ?_ ?_).symm
  · intro H
    exact Fin.succAbove_ne q b (congrArg Prod.snd H)
  · intro H
    exact Fin.succAbove_ne q a (congrArg Prod.fst H)

end Order

theorem enabled_letter_moves {n : Nat} (D : Domain (Fin (n+1)))
    (r : Order (Fin (n+1))) (j : Fin n) (hs : swapLetter r j ∈ D) :
    HasLift D r (r.atPos j.succ) ∧ HasDrop D r (r.atPos j.castSucc) := by
  have hc := r.atPos_consecutive j
  constructor
  · rw [hasLift_iff_rank]
    refine ⟨swapLetter r j,hs,hc.deleted_lower,?_⟩
    simp only [swapLetter,Order.rank_swapLabels,Equiv.swap_apply_right,Order.rank_atPos]
    exact Nat.lt_succ_self _
  · rw [hasDrop_iff_rank]
    refine ⟨swapLetter r j,hs,hc.deleted_upper,?_⟩
    simp only [swapLetter,Order.rank_swapLabels,Equiv.swap_apply_left,Order.rank_atPos]
    exact Nat.lt_succ_self _

def Locked {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) (j : Fin n) : Prop :=
  ¬ HasLift D r (r.atPos j.succ) ∧ ¬ HasDrop D r (r.atPos j.castSucc)

noncomputable def lockedCount {n : Nat} (D : Domain (Fin (n+1))) : Nat :=
  ∑ r ∈ D, ∑ j : Fin n, if Locked D r j then 1 else 0

theorem IsFull.letter_count {n : Nat} {D : Domain (Fin (n+1))} (hD : IsFull D)
    (r : Order (Fin (n+1))) (hr : r ∈ D) (j : Fin n) :
    (if ¬ HasLift D r (r.atPos j.succ) then 1 else 0) +
    (if ¬ HasDrop D r (r.atPos j.castSucc) then 1 else 0) +
    (if swapLetter r j ∈ D then 1 else 0) = 1 + (if Locked D r j then 1 else 0) := by
  have hc := r.atPos_consecutive j
  by_cases hs : swapLetter r j ∈ D
  · obtain ⟨hl,hd⟩ := enabled_letter_moves D r j hs
    simp [Locked,hs,hl,hd]
  · have H := hD.missing_swap r (swapLetter r j) _ _ hc.1 hr hs hc.2.1
      hc.swapped_comparison hc.2.2 hc.swap_agree
    by_cases hl : HasLift D r (r.atPos j.succ) <;>
      by_cases hd : HasDrop D r (r.atPos j.castSucc) <;> simp_all [Locked]

theorem top_has_no_lift {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) :
    ¬ HasLift D r (r.atPos 0) := by
  rw [hasLift_iff_rank]
  rintro ⟨s,_,_,h⟩
  simp only [Order.rank_atPos,Fin.val_zero] at h
  omega

theorem bottom_has_no_drop {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) :
    ¬ HasDrop D r (r.atPos (Fin.last n)) := by
  rw [hasDrop_iff_rank]
  rintro ⟨s,_,_,h⟩
  simp only [Order.rank_atPos,Fin.val_last] at h
  have H := s.rank_lt_size (r.atPos (Fin.last n))
  simp only [Fintype.card_fin] at H
  omega

theorem move_counts_per_order {n : Nat} (D : Domain (Fin (n+1))) (r : Order (Fin (n+1))) :
    (∑ x : Fin (n+1), if ¬ HasLift D r x then 1 else 0) +
    (∑ x : Fin (n+1), if ¬ HasDrop D r x then 1 else 0) =
      2 + ∑ j : Fin n,
        ((if ¬ HasLift D r (r.atPos j.succ) then 1 else 0) +
         (if ¬ HasDrop D r (r.atPos j.castSucc) then 1 else 0)) := by
  have hL : (∑ x : Fin (n+1), if ¬ HasLift D r x then 1 else 0) =
      1 + ∑ j : Fin n, if ¬ HasLift D r (r.atPos j.succ) then 1 else 0 := by
    rw [← Equiv.sum_comp r.positionEquiv.symm (fun x => if ¬ HasLift D r x then 1 else 0)]
    rw [Fin.sum_univ_succ]
    have hz : ¬ HasLift D r (r.positionEquiv.symm 0) := top_has_no_lift D r
    simp [hz,Order.atPos]
  have hR : (∑ x : Fin (n+1), if ¬ HasDrop D r x then 1 else 0) =
      (∑ j : Fin n, if ¬ HasDrop D r (r.atPos j.castSucc) then 1 else 0) + 1 := by
    rw [← Equiv.sum_comp r.positionEquiv.symm (fun x => if ¬ HasDrop D r x then 1 else 0)]
    rw [Fin.sum_univ_castSucc]
    have hz : ¬ HasDrop D r (r.positionEquiv.symm (Fin.last n)) := bottom_has_no_drop D r
    simp [hz,Order.atPos]
  rw [hL,hR,Finset.sum_add_distrib]
  omega

theorem sum_blocked_positions {n : Nat} (D : Domain (Fin (n+1))) :
    (∑ r ∈ D, ∑ x : Fin (n+1), if ¬ HasLift D r x then 1 else 0) = deletionSum D := by
  rw [Finset.sum_comm]
  change _ = ∑ x : Fin (n+1), (deleteDomain x D).card
  apply Finset.sum_congr rfl
  intro x _
  rw [← card_blockedOrders D x]
  simp only [blockedOrders,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem sum_nodrop_positions {n : Nat} (D : Domain (Fin (n+1))) :
    (∑ r ∈ D, ∑ x : Fin (n+1), if ¬ HasDrop D r x then 1 else 0) = deletionSum D := by
  rw [Finset.sum_comm]
  change _ = ∑ x : Fin (n+1), (deleteDomain x D).card
  apply Finset.sum_congr rfl
  intro x _
  rw [← card_noDropOrders D x]
  simp only [noDropOrders,Finset.card_eq_sum_ones,Finset.sum_filter]

/-- The second exact count in the gap proof, for actual full domains. -/
theorem IsFull.second_move_count {n : Nat} {D : Domain (Fin (n+1))} (hD : IsFull D) :
    2 * deletionSum D + adjacencyCount D = (n+2) * D.card + lockedCount D := by
  have H : ∀ r ∈ D,
      (∑ x : Fin (n+1), if ¬ HasLift D r x then 1 else 0) +
      (∑ x : Fin (n+1), if ¬ HasDrop D r x then 1 else 0) +
      (∑ j : Fin n, if swapLetter r j ∈ D then 1 else 0) =
        (n+2) + ∑ j : Fin n, if Locked D r j then 1 else 0 := by
    intro r hr
    rw [move_counts_per_order]
    have H := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => hD.letter_count r hr j)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] at H ⊢
    omega
  have HH := Finset.sum_congr rfl H
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at HH
  rw [sum_blocked_positions,sum_nodrop_positions,← adjacencyCount_eq_letters] at HH
  simpa only [lockedCount,two_mul,Nat.mul_comm,Nat.mul_add,Nat.add_mul] using HH

/-- Exact slack identity; no free-to-locked injection is assumed here. -/
theorem IsFull.gap_slack_identity {n : Nat} {D : Domain (Fin (n+1))} (hD : IsFull D) :
    3 * deletionSum D + freeCount D =
      (n+2) * D.card + gapCount D + frozenCount D + lockedCount D := by
  have H₁ := first_move_count D
  have H₂ := hD.second_move_count
  have H₃ := deletion_gap_adjacency_identity D
  omega

/-- This helper takes the injection explicitly. CDCert.FreeLocked.free_le_locked
proves it for maximal domains, and CDCert.Recurrences discharges the premise. -/
theorem IsFull.gap_bound_of_free_le_locked {n : Nat} {D : Domain (Fin (n+1))}
    (hD : IsFull D) (hinj : freeCount D ≤ lockedCount D) :
    gapCount D + (n+2) * D.card ≤ 3 * deletionSum D := by
  have H := hD.gap_slack_identity
  omega

#print axioms enabled_letter_moves
#print axioms IsFull.letter_count
#print axioms move_counts_per_order
#print axioms IsFull.second_move_count
#print axioms IsFull.gap_slack_identity
end Condorcet
