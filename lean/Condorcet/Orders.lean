import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext

/-! Actual orders and odd-profile Condorcet domains. No bound is assumed. -/
namespace Condorcet

/-- A Boolean comparison relation, read as "a is above b". -/
def IsStrictTotal {α : Type*} (r : α → α → Bool) : Prop :=
  (∀ a, r a a = false) ∧
  (∀ a b c, r a b = true → r b c = true → r a c = true) ∧
  (∀ a b, a ≠ b → r a b = true ∨ r b a = true)

def Order (α : Type*) := {r : α → α → Bool // IsStrictTotal r}

namespace Order
variable {α β : Type*}
instance : CoeFun (Order α) (fun _ => α → α → Bool) := ⟨Subtype.val⟩
noncomputable instance : DecidableEq (Order α) := Classical.decEq _
noncomputable instance [Fintype α] : Fintype (Order α) := by
  classical
  unfold Order
  infer_instance

@[ext] theorem ext {r s : Order α} (h : ∀ a b, r a b = s a b) : r = s := by
  apply Subtype.ext
  funext a b
  exact h a b

theorem irrefl (r : Order α) (a : α) : r a a = false := r.property.1 a

theorem trans (r : Order α) {a b c : α} (h₁ : r a b = true)
    (h₂ : r b c = true) : r a c = true := r.property.2.1 a b c h₁ h₂

theorem total (r : Order α) {a b : α} (h : a ≠ b) :
    r a b = true ∨ r b a = true := r.property.2.2 a b h

theorem asymmetric (r : Order α) {a b : α} (h : r a b = true) :
    r b a = false := by
  cases e : r b a with
  | false => rfl
  | true => have h' := r.trans h e; rw [r.irrefl] at h'; contradiction

/-- Restrict an order along an injection of the remaining alternatives. -/
def restrict (e : β ↪ α) (r : Order α) : Order β :=
  ⟨fun a b => r (e a) (e b),
    ⟨fun a => r.irrefl (e a),
      fun _ _ _ hab hbc => r.trans hab hbc,
      fun _ _ hab => r.total (fun h => hab (e.injective h))⟩⟩

@[simp] theorem restrict_apply (e : β ↪ α) (r : Order α) (a b : β) :
    restrict e r a b = r (e a) (e b) := rfl

end Order

abbrev Domain (α : Type*) := Finset (Order α)

/-- Strict simple majority for an explicitly indexed voter profile. -/
noncomputable def majority {α : Type*} {m : Nat} (v : Fin m → Order α)
    (a b : α) : Prop :=
  2 * (Finset.univ.filter (fun i => v i a b = true)).card > m

/-- Standard semantic definition: every odd voter profile has transitive majority. -/
def IsCondorcet {α : Type*} (D : Domain α) : Prop :=
  ∀ (m : Nat), Odd m → ∀ v : Fin m → Order α,
    (∀ i, v i ∈ D) → Transitive (majority v)

/-- A never-position clause expressed in the two comparisons involving x.
Positions 0,1,2 are first, middle, last. -/
def Never {α : Type*} (r : Order α) (x y z : α) (position : Fin 3) : Prop :=
  if position = 0 then r x y = false ∨ r x z = false
  else if position = 1 then r x y = r x z
  else r x y = true ∨ r x z = true

/-- Common never-condition on every triple, without assuming the characterization. -/
def ValueRestricted {α : Type*} (D : Domain α) : Prop :=
  ∀ a b c : α, a ≠ b → a ≠ c → b ≠ c →
    ∃ p : Fin 3,
      (∀ r ∈ D, Never r a b c p) ∨
      (∀ r ∈ D, Never r b a c p) ∨
      (∀ r ∈ D, Never r c a b p)

def ExtremeRestricted {α : Type*} (D : Domain α) : Prop :=
  ∀ a b c : α, a ≠ b → a ≠ c → b ≠ c →
    ∃ p : Fin 3, p ≠ 1 ∧
      ((∀ r ∈ D, Never r a b c p) ∨
       (∀ r ∈ D, Never r b a c p) ∨
       (∀ r ∈ D, Never r c a b p))

/-- Peak-pit Condorcet domains: semantic CD property and an extreme law per triple. -/
def IsPeakPit {α : Type*} (D : Domain α) : Prop :=
  IsCondorcet D ∧ ExtremeRestricted D

noncomputable def restrictDomain {α β : Type*} (e : β ↪ α) (D : Domain α) :
    Domain β := D.image (Order.restrict e)

@[simp] theorem mem_restrictDomain {α β : Type*} (e : β ↪ α) (D : Domain α)
    (s : Order β) : s ∈ restrictDomain e D ↔ ∃ r ∈ D, Order.restrict e r = s := by
  classical
  exact Finset.mem_image

theorem IsCondorcet.subset {α : Type*} {D E : Domain α}
    (hD : IsCondorcet D) (hED : E ⊆ D) : IsCondorcet E := by
  intro m hm v hv
  exact hD m hm v (fun i => hED (hv i))

/-- Actual domain restriction preserves odd-profile transitivity. -/
theorem IsCondorcet.restrict {α β : Type*} {D : Domain α}
    (hD : IsCondorcet D) (e : β ↪ α) : IsCondorcet (restrictDomain e D) := by
  classical
  intro m hm v hv
  have lift_exists : ∀ i, ∃ r ∈ D, Order.restrict e r = v i := by
    intro i
    exact (mem_restrictDomain e D (v i)).mp (hv i)
  choose w hw heq using lift_exists
  have hmaj : ∀ a b, majority v a b ↔ majority w (e a) (e b) := by
    intro a b
    have hc : (Finset.univ.filter (fun i => v i a b = true)) =
        (Finset.univ.filter (fun i => w i (e a) (e b) = true)) := by
      apply Finset.filter_congr
      intro i _
      rw [← heq i]
      rfl
    unfold majority
    rw [hc]
  intro a b c hab hbc
  exact (hmaj a c).mpr (hD m hm w hw ((hmaj a b).mp hab) ((hmaj b c).mp hbc))

theorem ExtremeRestricted.restrict {α β : Type*} {D : Domain α}
    (hD : ExtremeRestricted D) (e : β ↪ α) : ExtremeRestricted (restrictDomain e D) := by
  intro a b c hab hac hbc
  obtain ⟨p, hp, ht⟩ := hD (e a) (e b) (e c)
    (fun h => hab (e.injective h)) (fun h => hac (e.injective h))
    (fun h => hbc (e.injective h))
  refine ⟨p, hp, ?_⟩
  rcases ht with h | h | h
  · left
    intro s hs
    obtain ⟨r, hr, rfl⟩ := (mem_restrictDomain e D s).mp hs
    exact h r hr
  · right; left
    intro s hs
    obtain ⟨r, hr, rfl⟩ := (mem_restrictDomain e D s).mp hs
    exact h r hr
  · right; right
    intro s hs
    obtain ⟨r, hr, rfl⟩ := (mem_restrictDomain e D s).mp hs
    exact h r hr

theorem IsPeakPit.restrict {α β : Type*} {D : Domain α}
    (hD : IsPeakPit D) (e : β ↪ α) : IsPeakPit (restrictDomain e D) :=
  ⟨hD.1.restrict e, hD.2.restrict e⟩

end Condorcet
