/-
CDCert.PermsNodup — the list of all permutations of a duplicate-free list is
duplicate-free, and contains only rearrangements of it. Hence `orders n`
(the base universe used in the examples) is duplicate-free for every `n`,
proved once instead of by a quadratic kernel computation (which runs out of
memory at n = 6).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Examples

namespace CDCert.Examples

theorem mem_of_mem_insertAll {x : Nat} :
    ∀ {l p : List Nat}, p ∈ insertAll x l → ∀ y, y ∈ p ↔ y = x ∨ y ∈ l
  | [], p, h, y => by
    simp only [insertAll, List.mem_singleton] at h
    subst h
    simp
  | z :: zs, p, h, y => by
    simp only [insertAll, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · simp only [List.mem_cons]
    · simp only [List.mem_cons]
      rw [mem_of_mem_insertAll hq y]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem erase_of_mem_insertAll {x : Nat} :
    ∀ {l p : List Nat}, x ∉ l → p ∈ insertAll x l → p.erase x = l
  | [], p, _, h => by
    simp only [insertAll, List.mem_singleton] at h
    subst h
    exact List.erase_cons_head x []
  | z :: zs, p, hx, h => by
    simp only [insertAll, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact List.erase_cons_head x (z :: zs)
    · have hzx : z ≠ x := fun h => hx (h ▸ List.mem_cons_self)
      have hzx' : ¬(z == x) = true := by simpa using hzx
      rw [List.erase_cons_tail hzx',
        erase_of_mem_insertAll (fun h => hx (List.mem_cons_of_mem _ h)) hq]

theorem nodup_insertAll {x : Nat} : ∀ {l : List Nat}, x ∉ l → (insertAll x l).Nodup
  | [], _ => by simp [insertAll]
  | z :: zs, hx => by
    simp only [insertAll]
    rw [List.nodup_cons]
    constructor
    · intro h
      rw [List.mem_map] at h
      obtain ⟨q, _, hq⟩ := h
      have hzx : z = x := (List.cons.inj hq).1
      exact hx (hzx ▸ List.mem_cons_self)
    · unfold List.Nodup
      rw [List.pairwise_map]
      have ih : (insertAll x zs).Nodup :=
        nodup_insertAll (fun h => hx (List.mem_cons_of_mem _ h))
      exact List.Pairwise.imp (fun hab heq => hab (List.cons.inj heq).2) ih

theorem mem_perms : ∀ {l p : List Nat}, p ∈ perms l → ∀ y, y ∈ p ↔ y ∈ l
  | [], p, h, y => by
    simp only [perms, List.mem_singleton] at h
    subst h
    simp
  | x :: xs, p, h, y => by
    simp only [perms, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    rw [mem_of_mem_insertAll hp, mem_perms hq, List.mem_cons]

theorem nodup_perms : ∀ {l : List Nat}, l.Nodup → (perms l).Nodup
  | [], _ => by simp [perms]
  | x :: xs, h => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    simp only [perms]
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    constructor
    · intro q hq
      exact nodup_insertAll (fun hm => hx ((mem_perms hq x).mp hm))
    · have ih : (perms xs).Nodup := nodup_perms hxs
      refine List.Pairwise.imp_of_mem ?_ ih
      intro a b ha hb hab p hp p' hp' heq
      have hxa : x ∉ a := fun hm => hx ((mem_perms ha x).mp hm)
      have hxb : x ∉ b := fun hm => hx ((mem_perms hb x).mp hm)
      apply hab
      rw [← erase_of_mem_insertAll hxa hp, ← erase_of_mem_insertAll hxb hp', heq]

/-- The base universe of the examples is duplicate-free for every `n`. -/
theorem orders_nodup (n : Nat) : (orders n).Nodup :=
  nodup_perms List.nodup_range

end CDCert.Examples
