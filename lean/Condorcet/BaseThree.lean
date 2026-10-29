import Condorcet.TripleCharacterization
import Condorcet.Extremal

namespace Condorcet

/-- Each of the six coded orders, as an actual strict relation on Fin 3. -/
def relation3 (k : Fin 6) (a b : Fin 3) : Bool :=
  let t := Pattern.ofCode k
  match a.val, b.val with
  | 0, 1 => t.1
  | 0, 2 => t.2.1
  | 1, 0 => !t.1
  | 1, 2 => t.2.2
  | 2, 0 => !t.2.1
  | 2, 1 => !t.2.2
  | _, _ => false

theorem relation3_strict : ∀ k : Fin 6, IsStrictTotal (relation3 k) := by
  unfold IsStrictTotal
  decide

def orderOfCode (k : Fin 6) : Order (Fin 3) := ⟨relation3 k, relation3_strict k⟩

theorem orderPattern_ofCode : ∀ k : Fin 6,
    orderPattern (orderOfCode k) 0 1 2 = Pattern.ofCode k := by decide

theorem Pattern.ofCode_injective : Function.Injective Pattern.ofCode := by decide

theorem orderOfCode_injective : Function.Injective orderOfCode := by
  intro k l h
  apply Pattern.ofCode_injective
  have hh := congrArg (fun r => orderPattern r 0 1 2) h
  simpa only [orderPattern_ofCode] using hh

theorem orderPattern_injective :
    Function.Injective (fun r : Order (Fin 3) => orderPattern r 0 1 2) := by
  intro r s H
  have h01 : r 0 1 = s 0 1 := congrArg Prod.fst H
  have h02 : r 0 2 = s 0 2 := congrArg (fun t : Pattern => t.2.1) H
  have h12 : r 1 2 = s 1 2 := congrArg (fun t : Pattern => t.2.2) H
  have r10 := r.reverse_comparison (by decide : (0 : Fin 3) ≠ 1)
  have r20 := r.reverse_comparison (by decide : (0 : Fin 3) ≠ 2)
  have r21 := r.reverse_comparison (by decide : (1 : Fin 3) ≠ 2)
  have s10 := s.reverse_comparison (by decide : (0 : Fin 3) ≠ 1)
  have s20 := s.reverse_comparison (by decide : (0 : Fin 3) ≠ 2)
  have s21 := s.reverse_comparison (by decide : (1 : Fin 3) ≠ 2)
  apply Order.ext
  intro a b
  fin_cases a <;> fin_cases b <;> simp_all [Order.irrefl]

theorem patternCode_injective :
    Function.Injective (fun r : Order (Fin 3) => (orderPattern r 0 1 2).code) := by
  intro r s H
  apply orderPattern_injective
  calc
    orderPattern r 0 1 2 = Pattern.ofCode (orderPattern r 0 1 2).code :=
      (Pattern.decode_code _ (orderPattern_valid r (by decide) (by decide))).symm
    _ = Pattern.ofCode (orderPattern s 0 1 2).code := congrArg Pattern.ofCode H
    _ = orderPattern s 0 1 2 := Pattern.decode_code _ (orderPattern_valid s (by decide) (by decide))

set_option maxRecDepth 100000 in
theorem Pattern.commonNever_card_le_four : ∀ C : Finset (Fin 6),
    Pattern.CommonNever C → C.card ≤ 4 := by decide

theorem card_le_four {D : Domain (Fin 3)} (hD : IsCondorcet D) : D.card ≤ 4 := by
  classical
  have hC := Pattern.finite_characterization _ (patternFamily_closed hD
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2))
  have hc := Pattern.commonNever_card_le_four _ hC
  unfold patternFamily at hc
  rwa [Finset.card_image_of_injective _ patternCode_injective] at hc

def baseCodes : Finset (Fin 6) := {0, 1, 2, 3}

local instance (k : Fin 6) (a b c : Fin 3) (p : Fin 3) :
    Decidable (Never (orderOfCode k) a b c p) := by
  unfold Never
  infer_instance

/-- This explicit four-order family has an extreme never-law on every triple. -/
theorem baseCodes_extreme : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∃ p : Fin 3, p ≠ 1 ∧
      ((∀ k ∈ baseCodes, Never (orderOfCode k) a b c p) ∨
       (∀ k ∈ baseCodes, Never (orderOfCode k) b a c p) ∨
       (∀ k ∈ baseCodes, Never (orderOfCode k) c a b p)) := by
  decide

noncomputable def baseDomain : Domain (Fin 3) := baseCodes.image orderOfCode

theorem baseDomain_extreme : ExtremeRestricted baseDomain := by
  intro a b c hab hac hbc
  obtain ⟨p, hp, H⟩ := baseCodes_extreme a b c hab hac hbc
  refine ⟨p, hp, ?_⟩
  rcases H with H | H | H
  · left
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact H k hk
  · right; left
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact H k hk
  · right; right
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    exact H k hk

theorem baseDomain_card : baseDomain.card = 4 := by
  classical
  unfold baseDomain
  rw [Finset.card_image_of_injective _ orderOfCode_injective]
  decide

theorem f_three : f 3 = 4 := by
  apply Nat.le_antisymm
  · obtain ⟨D, hD, hc⟩ := exists_maximum_general 3
    rw [← hc]
    exact card_le_four hD
  · have H := card_le_f baseDomain_extreme.isPeakPit.1
    rwa [baseDomain_card] at H

theorem h_three : h 3 = 4 := by
  apply Nat.le_antisymm
  · calc h 3 ≤ f 3 := h_le_f 3
         _ = 4 := f_three
  · have H := card_le_h baseDomain_extreme.isPeakPit
    rwa [baseDomain_card] at H

#print axioms card_le_four
#print axioms f_three
#print axioms h_three
end Condorcet
