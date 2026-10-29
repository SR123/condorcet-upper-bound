/-
CDCert.K6.Base12 — the bottom- and top-indexed bases on six labels.

* `append_up_mem_orders`, `cons_up_mem_orders`: `L.map (up x) ++ [x]` and
  `x :: L.map (up x)` are orders of `0..k` for `L` an order of `0..k-1`, `x ≤ k`;
* `mem_baseB`, `mem_baseT`: the entries of `baseB k`, `baseT k` are orders of `0..k`;
* `block_maskOf_baseB`, `block_maskOf_baseT`: the 120-bit blocks of a mask over
  `base12` are the masks over `lexOrders 5` of the bottom and top slices;
* `maskOf_base12_mod`: its low 720 bits are its mask over `baseB 5`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.SliceClosure
import CDCert.K6.LexSem
import CDCert.K6.MaskLemmas
import CDCert.K6.LeafSem

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000

theorem perm_up_append {k x : Nat} (hx : x < k + 1) :
    ((List.range k).map (up x) ++ [x]).Perm (List.range (k + 1)) := by
  apply perm_of_nodup_of_mem_iff
  · rw [List.nodup_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [List.Nodup, List.pairwise_map]
      exact List.Pairwise.imp_of_mem (fun {a b} _ _ hab e => hab (up_injective x e)) List.nodup_range
    · intro a ha b hb
      rw [List.mem_singleton] at hb
      rw [hb]
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
      exact up_ne x c
  · exact List.nodup_range
  · intro b
    rw [List.mem_append, List.mem_map, List.mem_singleton, List.mem_range]
    constructor
    · rintro (⟨a, ha, rfl⟩ | rfl)
      · exact up_lt hx (List.mem_range.mp ha)
      · exact hx
    · intro hb
      by_cases hbx : b = x
      · exact Or.inr hbx
      · exact Or.inl ⟨down x b, List.mem_range.mpr (down_lt hb hbx hx), up_down hbx⟩

theorem append_up_mem_orders {k x : Nat} (hx : x < k + 1) {L : List Nat} (hL : L ∈ orders k) :
    L.map (up x) ++ [x] ∈ orders (k + 1) := by
  rw [mem_orders_iff] at hL ⊢
  exact ((hL.map (up x)).append_right [x]).trans (perm_up_append hx)

theorem cons_up_mem_orders {k x : Nat} (hx : x < k + 1) {L : List Nat} (hL : L ∈ orders k) :
    x :: L.map (up x) ∈ orders (k + 1) := by
  rw [mem_orders_iff] at hL ⊢
  exact (List.perm_append_singleton x (L.map (up x))).symm.trans
    (((hL.map (up x)).append_right [x]).trans (perm_up_append hx))

theorem mem_baseB {k : Nat} {M : List Nat} (h : M ∈ baseB k) : M ∈ orders (k + 1) := by
  unfold baseB at h
  obtain ⟨x, hx, hM⟩ := List.mem_flatMap.mp h
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
  exact append_up_mem_orders (List.mem_range.mp hx) (mem_lexOrders.mp hL)

theorem mem_baseT {k : Nat} {M : List Nat} (h : M ∈ baseT k) : M ∈ orders (k + 1) := by
  unfold baseT at h
  obtain ⟨x, hx, hM⟩ := List.mem_flatMap.mp h
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
  exact cons_up_mem_orders (List.mem_range.mp hx) (mem_lexOrders.mp hL)

theorem mem_base12 {M : List Nat} (h : M ∈ base12) : M ∈ orders 6 := by
  unfold base12 at h
  rcases List.mem_append.mp h with h | h
  · exact mem_baseB h
  · exact mem_baseT h

theorem length_lexOrders5' : (lexOrders 5).length = 120 := by decide

theorem length_baseB5 : (baseB 5).length = 720 := by decide

theorem block_maskOf_baseB (H : List Nat → Bool) {x : Nat} (hx : x < 6) :
    ((maskOf (baseB 5) H) >>> (120 * x)) % 2 ^ 120 = maskOf (lexOrders 5) (botP x H) := by
  unfold baseB
  have := maskOf_flatMap_block (fun x => (lexOrders 5).map (fun L => L.map (up x) ++ [x])) 120 H
    (List.range 6) (fun i _ => by rw [List.length_map, length_lexOrders5']) x (by simpa using hx)
  rw [this, List.getElem_range, maskOf_map]
  rfl

theorem block_maskOf_baseT (H : List Nat → Bool) {y : Nat} (hy : y < 6) :
    ((maskOf (baseT 5) H) >>> (120 * y)) % 2 ^ 120 = maskOf (lexOrders 5) (topP y H) := by
  unfold baseT
  have := maskOf_flatMap_block (fun x => (lexOrders 5).map (fun L => x :: L.map (up x))) 120 H
    (List.range 6) (fun i _ => by rw [List.length_map, length_lexOrders5']) y (by simpa using hy)
  rw [this, List.getElem_range, maskOf_map]
  rfl

theorem maskOf_base12_mod (H : List Nat → Bool) : maskOf base12 H % 2 ^ 720 = maskOf (baseB 5) H := by
  unfold base12
  rw [← length_baseB5, maskOf_append_mod]

theorem maskOf_base12_div (H : List Nat → Bool) : maskOf base12 H >>> 720 = maskOf (baseT 5) H := by
  unfold base12
  rw [Nat.shiftRight_eq_div_pow, ← length_baseB5, maskOf_append_div]

/-- The bottom blocks of a combined mask. -/
theorem block_base12_bot (H : List Nat → Bool) {x : Nat} (hx : x < 6) :
    block (maskOf base12 H) (120 * x) = maskOf (lexOrders 5) (botP x H) := by
  unfold block
  rw [← block_maskOf_baseB H hx, ← maskOf_base12_mod H]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 120
  · have : 120 * x + i < 720 := by omega
    simp [hi, this]
  · simp [hi]

/-- The top blocks of a combined mask. -/
theorem block_base12_top (H : List Nat → Bool) {y : Nat} (hy : y < 6) :
    block (maskOf base12 H) (720 + 120 * y) = maskOf (lexOrders 5) (topP y H) := by
  unfold block
  rw [← block_maskOf_baseT H hy, ← maskOf_base12_div H, Nat.shiftRight_add]

end CDCert.K6
