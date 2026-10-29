/-
CDCert.Deletion — deleting a label from orders written as lists, and the top
and bottom slices of a domain (support for C6 and for `Σ(D)` on the list side).

* `deleteLabel z L`: remove `z` and renumber the labels above `z` down by one.
  This is the list counterpart of restricting an order on `Fin (k+1)` along
  `z.succAbove : Fin k ↪ Fin (k+1)` (the bridge statement is Mathlib-side).
* `before_deleteLabel`: `before a b (deleteLabel z L) = before (up z a) (up z b) L`,
  where `up z` is `succAbove` on naturals.
* `deleteLabel_mem_orders`: deletion maps `orders (k+1)` into `orders k`.
* `bottomSlice z D`, `topSlice z D`: orders of `D` with `z` last / first,
  with `z` deleted.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.ListOrders

namespace CDCert.ListOrder

open CDCert CDCert.Examples

/-- `succAbove` on naturals: labels below `z` stay, the others move up. -/
def up (z a : Nat) : Nat := if a < z then a else a + 1

/-- Inverse of `up z` away from `z`. -/
def down (z a : Nat) : Nat := if a < z then a else a - 1

theorem up_injective (z : Nat) : Function.Injective (up z) := by
  intro a b h
  unfold up at h
  by_cases ha : a < z <;> by_cases hb : b < z <;> simp only [ha, hb, if_true, if_false] at h <;> omega

theorem up_ne (z a : Nat) : up z a ≠ z := by
  unfold up
  split <;> omega

theorem up_down {z a : Nat} (h : a ≠ z) : up z (down z a) = a := by
  unfold up down
  by_cases ha : a < z
  · simp [ha]
  · have : ¬ (a - 1 < z) := by omega
    simp only [ha, if_false, this]
    omega

theorem down_up (z a : Nat) : down z (up z a) = a := by
  unfold up down
  by_cases ha : a < z
  · simp [ha]
  · have : ¬ (a + 1 < z) := by omega
    simp only [ha, if_false, this]
    omega

/-- Remove `z` and renumber. -/
def deleteLabel (z : Nat) (L : List Nat) : List Nat :=
  (L.filter (fun a => a != z)).map (down z)

theorem map_up_deleteLabel (z : Nat) (L : List Nat) :
    (deleteLabel z L).map (up z) = L.filter (fun a => a != z) := by
  unfold deleteLabel
  rw [List.map_map]
  calc (L.filter (fun a => a != z)).map (up z ∘ down z)
      = (L.filter (fun a => a != z)).map id := by
        apply List.map_congr_left
        intro a ha
        rw [List.mem_filter] at ha
        have hne : a ≠ z := by simpa using ha.2
        exact up_down hne
    _ = L.filter (fun a => a != z) := List.map_id _

/-- **Comparisons after deletion.** -/
theorem before_deleteLabel (z a b : Nat) (L : List Nat) :
    before a b (deleteLabel z L) = before (up z a) (up z b) L := by
  rw [← before_map (up z) (up_injective z) a b, map_up_deleteLabel,
    before_filter (fun a => a != z) (by simpa using up_ne z a) (by simpa using up_ne z b)]

theorem mem_deleteLabel {z : Nat} {L : List Nat} {a : Nat} :
    a ∈ deleteLabel z L ↔ up z a ∈ L := by
  constructor
  · intro h
    have h' : up z a ∈ (deleteLabel z L).map (up z) := List.mem_map_of_mem h
    rw [map_up_deleteLabel, List.mem_filter] at h'
    exact h'.1
  · intro h
    have h' : up z a ∈ L.filter (fun a => a != z) := by
      rw [List.mem_filter]
      exact ⟨h, by simpa using up_ne z a⟩
    rw [← map_up_deleteLabel] at h'
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp h'
    rwa [up_injective z hba] at hb

theorem nodup_deleteLabel {z : Nat} {L : List Nat} (h : L.Nodup) : (deleteLabel z L).Nodup := by
  have h1 : ((deleteLabel z L).map (up z)).Nodup := by
    rw [map_up_deleteLabel]
    exact List.Pairwise.filter _ h
  exact List.Pairwise.of_map (up z) (fun a b hab heq => hab (heq ▸ rfl)) h1

/-- Duplicate-free lists with the same members are permutations of each other. -/
theorem perm_of_nodup_of_mem_iff {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  rw [h₁.count, h₂.count]
  by_cases ha : a ∈ l₁
  · rw [if_pos ha, if_pos ((h a).mp ha)]
  · rw [if_neg ha, if_neg (fun h' => ha ((h a).mpr h'))]

/-- Deletion maps orders on `k+1` labels to orders on `k` labels. -/
theorem deleteLabel_mem_orders {k z : Nat} (hz : z < k + 1) {L : List Nat}
    (hL : L ∈ orders (k + 1)) : deleteLabel z L ∈ orders k := by
  have hnd := nodup_deleteLabel (z := z) (nodup_of_mem_orders hL)
  rw [mem_orders_iff]
  apply perm_of_nodup_of_mem_iff hnd List.nodup_range
  intro a
  rw [mem_deleteLabel, mem_of_mem_orders hL, List.mem_range]
  unfold up
  split <;> omega

/-- Bottom slice: orders of `D` whose last label is `z`, with `z` deleted. -/
def bottomSlice (z : Nat) (D : List (List Nat)) : List (List Nat) :=
  (D.filter (fun L => L.getLast? == some z)).map (deleteLabel z)

/-- Top slice: orders of `D` whose first label is `z`, with `z` deleted. -/
def topSlice (z : Nat) (D : List (List Nat)) : List (List Nat) :=
  (D.filter (fun L => L.head? == some z)).map (deleteLabel z)

end CDCert.ListOrder
