import MajorityLaws

/-! Exact local majority/never-law calculation on all six strict orders of
three alternatives. This is independent of the finite window certificate. -/
namespace CondorcetUpperBounds

private def decForallFin : (n : Nat) → (P : Fin n → Prop) →
    [DecidablePred P] → Decidable (∀ i, P i)
  | 0, _, _ => isTrue (fun i => Fin.elim0 i)
  | n + 1, P, _ =>
    letI : Decidable (∀ i : Fin n, P i.succ) := decForallFin n (fun i => P i.succ)
    if h0 : P 0 then
      if hs : ∀ i : Fin n, P i.succ then isTrue (Fin.cases h0 hs)
      else isFalse (fun h => hs (fun i => h i.succ))
    else isFalse (fun h => h0 (h 0))

private def decExistsFin : (n : Nat) → (P : Fin n → Prop) →
    [DecidablePred P] → Decidable (∃ i, P i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n + 1, P, _ =>
    letI : Decidable (∃ i : Fin n, P i.succ) := decExistsFin n (fun i => P i.succ)
    if h0 : P 0 then isTrue ⟨0, h0⟩
    else if hs : ∃ i : Fin n, P i.succ then
      isTrue (by obtain ⟨i, hi⟩ := hs; exact ⟨i.succ, hi⟩)
    else isFalse (by
      intro h
      obtain ⟨i, hi⟩ := h
      exact Fin.cases (fun hh => h0 hh) (fun j hh => hs ⟨j, hh⟩) i hi)

local instance (n : Nat) (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := decForallFin n P
local instance (n : Nat) (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ i, P i) := decExistsFin n P

def rank3 (p : Fin 6) (a : Fin 3) : Nat :=
  match p.val, a.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2
  | 3, 0 => 2 | 3, 1 => 0 | 3, _ => 1
  | 4, 0 => 1 | 4, 1 => 2 | 4, _ => 0
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

def above3 (p : Fin 6) (a b : Fin 3) : Bool := decide (rank3 p a < rank3 p b)

def CommonNever3 (u v w : Fin 6) : Prop :=
  ∃ x : Fin 3, ∃ k : Fin 3,
    rank3 u x ≠ k.val ∧ rank3 v x ≠ k.val ∧ rank3 w x ≠ k.val

def Majority3 (u v w : Fin 6) (a b : Fin 3) : Bool :=
  median (above3 u a b) (above3 v a b) (above3 w a b)

/-- A common never-law excludes both cyclic orientations of majority. -/
theorem common_never_excludes_cycles : ∀ u v w : Fin 6,
    CommonNever3 u v w →
      ¬ (Majority3 u v w 0 1 = true ∧ Majority3 u v w 1 2 = true ∧
          Majority3 u v w 2 0 = true) ∧
      ¬ (Majority3 u v w 0 2 = true ∧ Majority3 u v w 2 1 = true ∧
          Majority3 u v w 1 0 = true) := by
  unfold CommonNever3
  decide

/-- On three alternatives a common never-law makes three-voter majority transitive. -/
theorem common_never_majority_transitive : ∀ u v w : Fin 6,
    CommonNever3 u v w → ∀ a b c : Fin 3,
      Majority3 u v w a b = true → Majority3 u v w b c = true →
      Majority3 u v w a c = true := by
  unfold CommonNever3
  decide

#print axioms common_never_excludes_cycles
#print axioms common_never_majority_transitive
end CondorcetUpperBounds
