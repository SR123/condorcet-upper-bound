/-
CDCert.K6.AllNat — `allNat` over appended lists, and as a universal statement.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs

namespace CDCert.K6

theorem allNat_append' (p : Nat → Bool) : ∀ (l₁ l₂ : List Nat), allNat p (l₁ ++ l₂) = (allNat p l₁ && allNat p l₂)
  | [], _ => by simp [allNat]
  | x :: xs, l₂ => by
    show (Bool.and (p x) (allNat p (xs ++ l₂))) = (Bool.and (Bool.and (p x) (allNat p xs)) (allNat p l₂))
    rw [allNat_append' p xs l₂, Bool.and_assoc]

theorem allNat_iff' (p : Nat → Bool) : ∀ (l : List Nat), allNat p l = true ↔ ∀ x, x ∈ l → p x = true
  | [] => by simp [allNat]
  | x :: xs => by
    show (Bool.and (p x) (allNat p xs)) = true ↔ _
    rw [Bool.and_eq_true, allNat_iff' p xs]
    simp

theorem allNat_cons' (p : Nat → Bool) (x : Nat) (xs : List Nat) : allNat p (x :: xs) = (p x && allNat p xs) := rfl
theorem allNat_nil' (p : Nat → Bool) : allNat p [] = true := rfl

end CDCert.K6
