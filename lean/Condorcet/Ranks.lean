import Condorcet.FullDomains

namespace Condorcet
namespace Order

variable {α : Type*} [Fintype α]

noncomputable def above (r : Order α) (x : α) : Finset α :=
  Finset.univ.filter (fun a => r a x = true)

@[simp] theorem mem_above (r : Order α) (a x : α) :
    a ∈ r.above x ↔ r a x = true := by simp [above]

noncomputable def rank (r : Order α) (x : α) : Nat := (r.above x).card

theorem above_ssubset (r : Order α) {a b : α} (hab : r a b = true) :
    r.above a ⊂ r.above b := by
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    exact (mem_above r x b).mpr (r.trans ((mem_above r x a).mp hx) hab)
  · intro heq
    have ha : a ∈ r.above b := (mem_above r a b).mpr hab
    rw [← heq] at ha
    have H := (mem_above r a a).mp ha
    rw [r.irrefl] at H
    contradiction

theorem rank_lt_of_above (r : Order α) {a b : α} (hab : r a b = true) :
    r.rank a < r.rank b := Finset.card_lt_card (r.above_ssubset hab)

theorem rank_lt_iff (r : Order α) {a b : α} :
    r.rank a < r.rank b ↔ r a b = true := by
  constructor
  · intro H
    have hne : a ≠ b := by intro h; subst b; exact Nat.lt_irrefl _ H
    rcases r.total hne with h | h
    · exact h
    · exact False.elim ((Nat.lt_asymm H) (r.rank_lt_of_above h))
  · exact r.rank_lt_of_above

theorem rank_lt_size (r : Order α) (x : α) : r.rank x < Fintype.card α := by
  have hs : r.above x ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro H
    have hx : x ∈ r.above x := by rw [H]; exact Finset.mem_univ _
    have hh := (mem_above r x x).mp hx
    rw [r.irrefl] at hh
    contradiction
  have hc := Finset.card_lt_card hs
  simpa only [rank, Finset.card_univ] using hc

noncomputable def rankIndex (r : Order α) (x : α) : Fin (Fintype.card α) :=
  ⟨r.rank x, r.rank_lt_size x⟩

theorem rankIndex_injective (r : Order α) : Function.Injective r.rankIndex := by
  intro a b H
  have heq : r.rank a = r.rank b := congrArg Fin.val H
  by_contra hne
  rcases r.total hne with h | h
  · have hh := r.rank_lt_of_above h
    omega
  · have hh := r.rank_lt_of_above h
    omega

/-- The actual rank bijection, giving the permutation/slot representation of an order. -/
noncomputable def rankEquiv (r : Order α) : α ≃ Fin (Fintype.card α) :=
  Equiv.ofBijective r.rankIndex
    ((Fintype.bijective_iff_injective_and_card r.rankIndex).mpr ⟨r.rankIndex_injective,by simp⟩)

@[simp] theorem rankEquiv_apply (r : Order α) (x : α) :
    (r.rankEquiv x).val = r.rank x := rfl

noncomputable def atPosition (r : Order α) (p : Fin (Fintype.card α)) : α :=
  r.rankEquiv.symm p

@[simp] theorem rank_atPosition (r : Order α) (p : Fin (Fintype.card α)) :
    r.rank (r.atPosition p) = p.val := congrArg Fin.val (r.rankEquiv.apply_symm_apply p)

@[simp] theorem atPosition_rank (r : Order α) (x : α) :
    r.atPosition (r.rankIndex x) = x := r.rankEquiv.symm_apply_apply x

#print axioms rank_lt_iff
#print axioms rankEquiv
#print axioms rank_atPosition
end Order
end Condorcet
