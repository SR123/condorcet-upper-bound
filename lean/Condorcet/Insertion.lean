import Condorcet.Ranks
import Mathlib.Data.Fintype.Option

namespace Condorcet
namespace Order
variable {α : Type*} [Fintype α]

def someEmbedding : α ↪ Option α := ⟨Option.some, fun _ _ h => Option.some.inj h⟩

noncomputable def insertionRelation (r : Order α) (t : Fin (Fintype.card α + 1)) :
    Option α → Option α → Bool
  | none, none => false
  | none, some b => decide (t.val ≤ r.rank b)
  | some a, none => decide (r.rank a < t.val)
  | some a, some b => r a b

theorem insertionRelation_strict (r : Order α) (t : Fin (Fintype.card α + 1)) :
    IsStrictTotal (insertionRelation r t) := by
  constructor
  · intro a
    cases a <;> simp [insertionRelation, Order.irrefl]
  constructor
  · intro a b c hab hbc
    cases a <;> cases b <;> cases c
    · simp [insertionRelation] at hab
    · simp [insertionRelation] at hab
    · simp only [insertionRelation, decide_eq_true_eq] at hab hbc
      omega
    · have hbc' := r.rank_lt_of_above hbc
      simp only [insertionRelation, decide_eq_true_eq] at hab ⊢
      omega
    · simp [insertionRelation] at hbc
    · apply r.rank_lt_iff.mp
      simp only [insertionRelation, decide_eq_true_eq] at hab hbc
      omega
    · have hab' := r.rank_lt_of_above hab
      simp only [insertionRelation, decide_eq_true_eq] at hbc ⊢
      omega
    · exact r.trans hab hbc
  · intro a b hab
    cases a <;> cases b
    · exact False.elim (hab rfl)
    · simp only [insertionRelation, decide_eq_true_eq]
      omega
    · simp only [insertionRelation, decide_eq_true_eq]
      omega
    · exact r.total (fun h => hab (congrArg Option.some h))

/-- Insert a new alternative `none` at the specified slot of the actual order. -/
noncomputable def insertAt (r : Order α) (t : Fin (Fintype.card α + 1)) : Order (Option α) :=
  ⟨insertionRelation r t, insertionRelation_strict r t⟩

@[simp] theorem insertAt_some_some (r : Order α) (t : Fin (Fintype.card α + 1)) (a b : α) :
    r.insertAt t (some a) (some b) = r a b := rfl

@[simp] theorem restrict_insertAt (r : Order α) (t : Fin (Fintype.card α + 1)) :
    restrict someEmbedding (r.insertAt t) = r := by
  apply Order.ext
  intro a b
  rfl

theorem insertAt_ne_of_lt (r : Order α) {t u : Fin (Fintype.card α + 1)} (htu : t < u) :
    r.insertAt t ≠ r.insertAt u := by
  intro H
  have ht : t.val < Fintype.card α := by have hu := u.isLt; have htu' := htu; change t.val < u.val at htu'; omega
  let p : Fin (Fintype.card α) := ⟨t.val,ht⟩
  let a := r.atPosition p
  have ha : r.rank a = t.val := r.rank_atPosition p
  have hh := congrArg (fun s : Order (Option α) => s (some a) none) H
  change decide (r.rank a < t.val) = decide (r.rank a < u.val) at hh
  rw [ha] at hh
  have htu' : t.val < u.val := htu
  simp [htu'] at hh

theorem insertAt_injective (r : Order α) : Function.Injective r.insertAt := by
  intro t u H
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact r.insertAt_ne_of_lt hlt H
  · exact r.insertAt_ne_of_lt hgt H.symm

noncomputable def insertionCut (s : Order (Option α)) : Finset α :=
  Finset.univ.filter (fun a => s (some a) none = true)

@[simp] theorem mem_insertionCut (s : Order (Option α)) (a : α) :
    a ∈ s.insertionCut ↔ s (some a) none = true := by simp [insertionCut]

/-- The cut made by the new alternative is an initial segment of the old order. -/
theorem insertionCut_iff_rank (s : Order (Option α)) (a : α) :
    s (some a) none = true ↔ (restrict someEmbedding s).rank a < s.insertionCut.card := by
  let r := restrict someEmbedding s
  constructor
  · intro ha
    have hs : r.above a ⊂ s.insertionCut := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro b hb
        have hba : s (some b) (some a) = true := (mem_above r b a).mp hb
        exact (mem_insertionCut s b).mpr (s.trans hba ha)
      · intro heq
        have hh : a ∈ s.insertionCut := (mem_insertionCut s a).mpr ha
        rw [← heq] at hh
        have hh' := (mem_above r a a).mp hh
        rw [r.irrefl] at hh'
        contradiction
    exact Finset.card_lt_card hs
  · intro hlt
    by_contra ha
    have hna : s none (some a) = true := (s.total (by simp : (some a : Option α) ≠ none)).resolve_left ha
    have hs : s.insertionCut ⊆ r.above a := by
      intro b hb
      exact (mem_above r b a).mpr (s.trans ((mem_insertionCut s b).mp hb) hna)
    have hc := Finset.card_le_card hs
    change s.insertionCut.card ≤ r.rank a at hc
    exact Nat.not_lt_of_ge hc hlt

noncomputable def insertionSlot (s : Order (Option α)) : Fin (Fintype.card α + 1) :=
  ⟨s.insertionCut.card, by
    have H := Finset.card_le_card (Finset.subset_univ s.insertionCut)
    simp only [Finset.card_univ] at H
    omega⟩

/-- Every actual order is uniquely an insertion into its deleted order. -/
theorem reconstruct_insertion (s : Order (Option α)) :
    (restrict someEmbedding s).insertAt s.insertionSlot = s := by
  have hSome : ∀ a : α, (restrict someEmbedding s).insertAt s.insertionSlot (some a) none =
      s (some a) none := by
    intro a
    change decide ((restrict someEmbedding s).rank a < s.insertionCut.card) = s (some a) none
    simp only [← s.insertionCut_iff_rank a, Bool.decide_coe]
  apply Order.ext
  intro a b
  cases a with
  | none =>
    cases b with
    | none => rw [Order.irrefl, Order.irrefl]
    | some b =>
      rw [Order.reverse_comparison _ (by simp : (some b : Option α) ≠ none),
        s.reverse_comparison (by simp : (some b : Option α) ≠ none), hSome b]
  | some a =>
    cases b with
    | none => exact hSome a
    | some b => rfl

#print axioms insertionRelation_strict
#print axioms insertAt_injective
#print axioms insertionCut_iff_rank
#print axioms reconstruct_insertion
end Order
end Condorcet
