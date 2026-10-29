import Condorcet.Orders
import MajorityLaws
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod

namespace Condorcet
open CondorcetUpperBounds

namespace Order

theorem reverse_comparison {α : Type*} (r : Order α) {a b : α} (hne : a ≠ b) :
    r b a = !(r a b) := by
  cases e : r a b with
  | false =>
    have h := (r.total hne).resolve_left (by simp [e])
    exact h
  | true => exact r.asymmetric e

end Order

theorem median_complement : ∀ a b c : Bool,
    median (!a) (!b) (!c) = !(median a b c) := by decide

def tripleProfile {α : Type*} (u v w : Order α) : Fin 3 → Order α :=
  fun i => if i = 0 then u else if i = 1 then v else w

theorem majority_three {α : Type*} (u v w : Order α) (a b : α) :
    majority (tripleProfile u v w) a b ↔ median (u a b) (v a b) (w a b) = true := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  cases e₁ : u a b <;> cases e₂ : v a b <;> cases e₃ : w a b <;>
    simp [majority, hu, Finset.filter_insert, Finset.filter_singleton, tripleProfile, e₁, e₂, e₃, median]

/-- A semantic Condorcet domain makes the pairwise median an actual strict order. -/
def medianOrder {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    (u v w : Order α) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) : Order α := by
  refine ⟨fun a b => median (u a b) (v a b) (w a b), ?_, ?_, ?_⟩
  · intro a
    simp [Order.irrefl, median]
  · intro a b c hab hbc
    have H := hD 3 (by decide) (tripleProfile u v w) (by
      intro i
      fin_cases i <;> simp [tripleProfile, hu, hv, hw])
    exact (majority_three u v w a c).mp
      (H ((majority_three u v w a b).mpr hab) ((majority_three u v w b c).mpr hbc))
  · intro a b hab
    change median (u a b) (v a b) (w a b) = true ∨
      median (u b a) (v b a) (w b a) = true
    cases e : median (u a b) (v a b) (w a b) with
    | true => exact Or.inl rfl
    | false =>
      right
      rw [u.reverse_comparison hab, v.reverse_comparison hab, w.reverse_comparison hab,
        median_complement, e]
      rfl

@[simp] theorem medianOrder_apply {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    (u v w : Order α) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) (a b : α) :
    medianOrder hD u v w hu hv hw a b = median (u a b) (v a b) (w a b) := rfl

/-- Canonical coordinates contain exactly one orientation of each unordered pair. -/
def Pair (n : Nat) := {ab : Fin n × Fin n // ab.1 < ab.2}

noncomputable instance (n : Nat) : Fintype (Pair n) := by
  classical
  unfold Pair
  infer_instance

def encode {n : Nat} (r : Order (Fin n)) : Pair n → Bool :=
  fun ab => r ab.val.1 ab.val.2

theorem encode_injective {n : Nat} : Function.Injective (@encode n) := by
  intro r s h
  apply Order.ext
  intro a b
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact congrFun h ⟨(a,b), hab⟩
  · rw [r.irrefl, s.irrefl]
  · have hrev : r b a = s b a := congrFun h ⟨(b,a), hba⟩
    rw [r.reverse_comparison (ne_of_lt hba), s.reverse_comparison (ne_of_lt hba), hrev]

@[simp] theorem encode_medianOrder {n : Nat} {D : Domain (Fin n)} (hD : IsCondorcet D)
    (u v w : Order (Fin n)) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) :
    encode (medianOrder hD u v w hu hv hw) = comparisonMajority (encode u) (encode v) (encode w) := rfl

#print axioms majority_three
#print axioms medianOrder
#print axioms encode_injective
end Condorcet
