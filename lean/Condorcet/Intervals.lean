import Condorcet.ExtremeFull
import Condorcet.DeletionBridge

namespace Condorcet

/-- Each comparison stays fixed between any two slots where it has the same value. -/
theorem insertion_comparison_between {α : Type*} [Fintype α] (P : Order α)
    {l t u : Fin (Fintype.card α + 1)} (hlt : l ≤ t) (htu : t ≤ u)
    (a b : Option α) (v : Bool) (hl : P.insertAt l a b = v) (hu : P.insertAt u a b = v) :
    P.insertAt t a b = v := by
  cases a <;> cases b <;> cases v <;>
    simp_all [Order.insertAt, Order.insertionRelation] <;> omega

/-- An extreme never-law cuts out an interval of insertion slots. -/
theorem extreme_never_between {α : Type*} [Fintype α] (P : Order α)
    {l t u : Fin (Fintype.card α + 1)} (hlt : l ≤ t) (htu : t ≤ u)
    (a b c : Option α) (p : Fin 3) (hp : p ≠ 1)
    (hl : Never (P.insertAt l) a b c p) (hu : Never (P.insertAt u) a b c p) :
    Never (P.insertAt t) a b c p := by
  fin_cases p <;> cases a <;> cases b <;> cases c <;>
    simp_all [Never, Order.insertAt, Order.insertionRelation] <;> (try omega)
  all_goals
    rename_i a b
    cases hv : P a b <;> simp_all <;> omega

@[simp] theorem never_transport {α β : Type*} (e : α ≃ β) (r : Order α)
    (a b c : β) (p : Fin 3) :
    Never (Order.transport e r) a b c p ↔ Never r (e.symm a) (e.symm b) (e.symm c) p := by
  simp [Never]

theorem holdsLaw_insertion_between {α : Type*} [Fintype α] {n : Nat}
    (e : Option α ≃ Fin n) (P : Order α)
    {l t u : Fin (Fintype.card α + 1)} (hlt : l ≤ t) (htu : t ≤ u)
    (T : Triple n) (law : Fin 3 × Fin 3) (hp : law.2 ≠ 1)
    (hl : HoldsLaw (Order.transport e (P.insertAt l)) T law)
    (hu : HoldsLaw (Order.transport e (P.insertAt u)) T law) :
    HoldsLaw (Order.transport e (P.insertAt t)) T law := by
  by_cases hx : law.1 = 0 <;> by_cases hy : law.1 = 1 <;>
    simp only [HoldsLaw, hx, hy, if_true, if_false, never_transport] at hl hu ⊢ <;>
    exact extreme_never_between P hlt htu _ _ _ law.2 hp hl hu

theorem holdsPairs_insertion_between {α : Type*} [Fintype α] {n : Nat}
    (e : Option α ≃ Fin n) (P : Order α)
    {l t u : Fin (Fintype.card α + 1)} (hlt : l ≤ t) (htu : t ≤ u)
    (Q : FixedPairs n)
    (hl : HoldsPairs Q (Order.transport e (P.insertAt l)))
    (hu : HoldsPairs Q (Order.transport e (P.insertAt u))) :
    HoldsPairs Q (Order.transport e (P.insertAt t)) := by
  intro i v hv
  exact insertion_comparison_between P hlt htu _ _ v (hl i v hv) (hu i v hv)

@[simp] theorem mem_transportDomain {α β : Type*} (e : α ≃ β) (D : Domain α)
    (r : Order β) : r ∈ transportDomain e D ↔ Order.transport e.symm r ∈ D := by
  classical
  unfold transportDomain
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    simpa using hs
  · intro h
    exact ⟨Order.transport e.symm r,h,by simp⟩

/-- Every actual insertion fibre of a full extreme-plus-pair domain is an interval. -/
theorem IsExtremeFull.insertionSlots_interval {n : Nat} {D : Domain (Fin (n + 1))}
    (hD : IsExtremeFull D) (x : Fin (n + 1)) (P : Order (Fin n))
    {l t u : Fin (Fintype.card (Fin n) + 1)} (hlt : l ≤ t) (htu : t ≤ u)
    (hl : l ∈ insertionSlots (optionDomain x D) P)
    (hu : u ∈ insertionSlots (optionDomain x D) P) :
    t ∈ insertionSlots (optionDomain x D) P := by
  obtain ⟨L,Q,rfl⟩ := hD
  simp only [mem_insertionSlots, optionDomain, mem_transportDomain, Equiv.symm_symm,
    mem_extremeFullDomain] at hl hu ⊢
  constructor
  · intro T
    exact holdsLaw_insertion_between (deletionEquiv x) P hlt htu T (L.val T)
      (L.property T) (hl.1 T) (hu.1 T)
  · exact holdsPairs_insertion_between (deletionEquiv x) P hlt htu Q hl.2 hu.2

#print axioms extreme_never_between
#print axioms IsExtremeFull.insertionSlots_interval
end Condorcet
