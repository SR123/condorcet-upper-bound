import Std

/-!
# Majority preservation of comparison clauses

The Boolean clauses corresponding to never-first, never-last, never-middle,
and fixed comparisons are preserved under coordinatewise majority.
This module treats Boolean clauses. The semantic order-theoretic step and
its connection to Condorcet domains are proved separately in Condorcet.Majority
and Condorcet.MedianClosure; the complete bounds are stated in CDCert.Main.
-/
namespace CondorcetUpperBounds

def median (a b c : Bool) : Bool := (a && b) || (b && c) || (c && a)

theorem median_self : ∀ a b : Bool, median a b a = a := by decide

theorem median_same : ∀ a b : Bool, median a a b = a := by decide

theorem median_true_false : ∀ a : Bool, median true false a = a := by decide

theorem median_preserves_never_first : ∀ a b c d e f : Bool,
    (a = false ∨ b = false) → (c = false ∨ d = false) →
    (e = false ∨ f = false) →
    median a c e = false ∨ median b d f = false := by decide

theorem median_preserves_never_last : ∀ a b c d e f : Bool,
    (a = true ∨ b = true) → (c = true ∨ d = true) →
    (e = true ∨ f = true) →
    median a c e = true ∨ median b d f = true := by decide

theorem median_preserves_never_middle : ∀ a b c d e f : Bool,
    a = b → c = d → e = f → median a c e = median b d f := by decide

inductive ComparisonLaw (I : Type)
  | neverFirst : I → I → ComparisonLaw I
  | neverLast : I → I → ComparisonLaw I
  | neverMiddle : I → I → ComparisonLaw I
  | fixed : I → Bool → ComparisonLaw I

def ComparisonLaw.Holds {I : Type} : ComparisonLaw I → (I → Bool) → Prop
  | .neverFirst i j, v => v i = false ∨ v j = false
  | .neverLast i j, v => v i = true ∨ v j = true
  | .neverMiddle i j, v => v i = v j
  | .fixed i b, v => v i = b

def comparisonMajority {I : Type} (u v w : I → Bool) : I → Bool :=
  fun i => median (u i) (v i) (w i)

theorem law_preserved {I : Type} (law : ComparisonLaw I) (u v w : I → Bool)
    (hu : law.Holds u) (hv : law.Holds v) (hw : law.Holds w) :
    law.Holds (comparisonMajority u v w) := by
  cases law with
  | neverFirst i j =>
    exact median_preserves_never_first (u i) (u j) (v i) (v j) (w i) (w j) hu hv hw
  | neverLast i j =>
    exact median_preserves_never_last (u i) (u j) (v i) (v j) (w i) (w j) hu hv hw
  | neverMiddle i j =>
    exact median_preserves_never_middle (u i) (u j) (v i) (v j) (w i) (w j) hu hv hw
  | fixed i b =>
    change median (u i) (v i) (w i) = b
    rw [hu, hv, hw]
    exact median_self b b

def Satisfies {I : Type} (laws : List (ComparisonLaw I)) (v : I → Bool) : Prop :=
  ∀ law, law ∈ laws → law.Holds v

theorem conjunction_preserved {I : Type} (laws : List (ComparisonLaw I))
    (u v w : I → Bool) (hu : Satisfies laws u) (hv : Satisfies laws v)
    (hw : Satisfies laws w) : Satisfies laws (comparisonMajority u v w) := by
  intro law hlaw
  exact law_preserved law u v w (hu law hlaw) (hv law hlaw) (hw law hlaw)

/-- Majority fixes any coordinate on which the two reference vectors agree. -/
theorem projection_fixes_agreement {I : Type} (s t v : I → Bool) (i : I)
    (h : s i = t i) : comparisonMajority s t v i = s i := by
  change median (s i) (t i) (v i) = s i
  rw [← h]
  exact median_same (s i) (v i)

/-- At most one differing coordinate, allowing a stationary step. -/
def OneCoordinate {I : Type} (u v : I → Bool) : Prop :=
  u = v ∨ ∃ k : I, ∀ i, i ≠ k → u i = v i

theorem projection_preserves_step {I : Type} (s t u v : I → Bool)
    (h : OneCoordinate u v) :
    OneCoordinate (comparisonMajority s t u) (comparisonMajority s t v) := by
  cases h with
  | inl h => exact Or.inl (congrArg (comparisonMajority s t) h)
  | inr h =>
    obtain ⟨k, hk⟩ := h
    apply Or.inr
    refine ⟨k, ?_⟩
    intro i hi
    change median (s i) (t i) (u i) = median (s i) (t i) (v i)
    rw [hk i hi]

#print axioms law_preserved
#print axioms conjunction_preserved
#print axioms projection_fixes_agreement
#print axioms projection_preserves_step
end CondorcetUpperBounds
