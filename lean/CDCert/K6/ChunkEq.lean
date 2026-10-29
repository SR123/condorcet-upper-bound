/-
CDCert.K6.ChunkEq — equality of two lists from equality of all their chunks, so that a long
kernel-evaluated list equality can be split into independent checks.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
namespace CDCert.K6

set_option autoImplicit false

theorem list_eq_of_chunks {α : Type} (l₁ l₂ : List α) (c n : Nat) (hc : 0 < c)
    (h₁ : l₁.length = c * n) (h₂ : l₂.length = c * n)
    (h : ∀ i, i < n → (l₁.drop (c * i)).take c = (l₂.drop (c * i)).take c) : l₁ = l₂ := by
  apply List.ext_getElem (h₁.trans h₂.symm)
  intro j hj1 hj2
  have hjc : j / c < n := by
    rw [h₁] at hj1
    exact (Nat.div_lt_iff_lt_mul hc).mpr (by rw [Nat.mul_comm]; exact hj1)
  have hmod : j % c < c := Nat.mod_lt j hc
  have hdec : c * (j / c) + j % c = j := Nat.div_add_mod j c
  have e := congrArg (fun l => l[j % c]?) (h (j / c) hjc)
  simp only [List.getElem?_take, List.getElem?_drop, if_pos hmod, hdec] at e
  rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2] at e
  exact Option.some.inj e

end CDCert.K6
