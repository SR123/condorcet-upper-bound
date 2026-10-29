/-
CDCert.K6.LexSem — `lexOrders k` lists exactly the orders on `k` labels.

* `mem_lexPermsAux`: for a duplicate-free `l` of length `n`, the members of
  `lexPermsAux n l` are exactly the permutations of `l`;
* `mem_lexOrders`: `L ∈ lexOrders k ↔ L ∈ orders k`;
* `getElem_lexIdx`: on lists of orders whose `lexIdx` values are the positions
  (checked by the kernel for `k = 4, 5`), `lexIdx L` is the position of `L`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex
import CDCert.K6.Defs5

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

theorem mem_lexPermsAux : ∀ (n : Nat) (l : List Nat), l.Nodup → l.length = n →
    ∀ p, p ∈ lexPermsAux n l ↔ p.Perm l
  | 0, l, _, hl, p => by
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp only [lexPermsAux, List.mem_singleton]
    exact ⟨fun h => h ▸ List.Perm.refl _, fun h => List.perm_nil.mp h⟩
  | n + 1, l, hnd, hl, p => by
    simp only [lexPermsAux, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, q, hq, rfl⟩
      have hq' := (mem_lexPermsAux n (l.erase x) (hnd.erase x)
        (by rw [List.length_erase_of_mem hx]; omega) q).mp hq
      exact (hq'.cons x).trans (List.perm_cons_erase hx).symm
    · intro hp
      have hlen : p.length = n + 1 := by rw [hp.length_eq, hl]
      match p, hlen with
      | x :: q, _ =>
        have hx : x ∈ l := hp.subset List.mem_cons_self
        refine ⟨x, hx, q, ?_, rfl⟩
        rw [mem_lexPermsAux n (l.erase x) (hnd.erase x)
          (by rw [List.length_erase_of_mem hx]; omega)]
        exact (hp.trans (List.perm_cons_erase hx)).cons_inv

theorem mem_lexOrders {k : Nat} {L : List Nat} : L ∈ lexOrders k ↔ L ∈ orders k := by
  rw [mem_orders_iff]
  exact mem_lexPermsAux k (List.range k) List.nodup_range List.length_range L

/-- If `lexIdx` is the position on the list `P`, then `lexIdx L` is the position of
every member `L`. -/
theorem getElem_lexIdx {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    {L : List Nat} (hL : L ∈ P) : ∃ h : lexIdx L < P.length, P[lexIdx L] = L := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have h1 : (P.map lexIdx)[i]'(by rw [List.length_map]; exact hi) = i := by
    rw [List.getElem_of_eq hP (by rw [List.length_map]; exact hi), List.getElem_range]
  rw [List.getElem_map] at h1
  rw [h1]
  exact ⟨hi, rfl⟩

theorem lexIdx_getElem {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    (i : Nat) (hi : i < P.length) : lexIdx P[i] = i := by
  have h1 : (P.map lexIdx)[i]'(by rw [List.length_map]; exact hi) = i := by
    rw [List.getElem_of_eq hP (by rw [List.length_map]; exact hi), List.getElem_range]
  rw [List.getElem_map] at h1
  exact h1

end CDCert.K6
