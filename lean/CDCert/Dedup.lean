/-
CDCert.Dedup — verified, kernel-reducible deduplication of lists.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no axioms beyond Lean's standard ones,
no `native_decide`.

`dedup` keeps the first occurrence of every element. It is defined by
structural recursion with an accumulator, so the kernel reduces it directly
(each comparison is a `DecidableEq` call; nothing is evaluated by the compiler).
-/

namespace CDCert

section
variable {β : Type} [DecidableEq β]

/-- Accumulator form: `acc` holds the distinct elements seen so far, newest first. -/
def dedupAux : List β → List β → List β
  | [], acc => acc.reverse
  | x :: xs, acc => if x ∈ acc then dedupAux xs acc else dedupAux xs (x :: acc)

/-- Remove duplicates, keeping the first occurrence of each element. -/
def dedup (l : List β) : List β := dedupAux l []

theorem mem_dedupAux (l acc : List β) (y : β) :
    y ∈ dedupAux l acc ↔ y ∈ l ∨ y ∈ acc := by
  induction l generalizing acc with
  | nil => simp [dedupAux]
  | cons x xs ih =>
    simp only [dedupAux]
    split
    · rename_i hx
      rw [ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((rfl | h) | h)
        · exact Or.inr hx
        · exact Or.inl h
        · exact Or.inr h
    · rw [ih, List.mem_cons, List.mem_cons]
      constructor
      · rintro (h | rfl | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h
      · rintro ((rfl | h) | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- Deduplication neither loses nor invents elements. -/
@[simp] theorem mem_dedup (l : List β) (y : β) : y ∈ dedup l ↔ y ∈ l := by
  simp [dedup, mem_dedupAux]

theorem nodup_dedupAux (l acc : List β) (h : acc.Nodup) : (dedupAux l acc).Nodup := by
  induction l generalizing acc with
  | nil =>
    simp only [dedupAux]
    unfold List.Nodup at *
    rw [List.pairwise_reverse]
    exact List.Pairwise.imp (fun hab hba => hab hba.symm) h
  | cons x xs ih =>
    simp only [dedupAux]
    split
    · exact ih acc h
    · rename_i hx
      exact ih (x :: acc) (List.nodup_cons.mpr ⟨hx, h⟩)

/-- The output of `dedup` has no repetitions. -/
theorem nodup_dedup (l : List β) : (dedup l).Nodup :=
  nodup_dedupAux l [] List.nodup_nil

end

end CDCert
