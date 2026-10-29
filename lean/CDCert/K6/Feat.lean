/-
CDCert.K6.Feat — the finite features at list level, and how they split over slices.

A `k`-domain is a predicate `H` on the orders of `0..k-1` (lists, top to bottom).

* `card k H`: number of orders of `H`;
* `adjAt k j H`: number of orders `M` of `H` whose swap at positions `j`, `j + 1`
  (`swapAt j M`) is again in `H`; `adj k H = Σ_{j < k-1} adjAt k j H` (directed adjacent
  swaps); `cost10 J`: the weighted count `a₁ + 2a₂ + 2a₃ + 2a₄ + 2a₅ + a₆` of a seven-domain
  (positions numbered from 1 in the paper, from 0 here), i.e. `10 C(J)`;
* `countP_orders_succ_last`, `countP_orders_succ_first`: counting over the orders of
  `0..k` by their last (first) label;
* `card_succ_bot`, `card_succ_top`, `adjAt_succ_bot`, `adjAt_succ_top`: the same for the
  features and the bottom / top slices `botP`, `topP`;
* `adj6_split`: `adj 6 H = Σ_x adj 5 (B_x H) + Σ_y adjAt 5 3 (T_y H)`;
* `cost10_split`: `cost10 J = Σ_z adj 6 (B_z J) + Σ_w adj 6 (T_w J)` ("the sum of `A(H)` over
  all six-slices is `10 C(J)`");
* `card_relabel`, `adjAt_relabel`, `adj_relabel`: invariance under relabelling.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.SixSemA
import CDCert.K6.SliceClosure
import CDCert.K6.Lex5

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-! ### Features -/

/-- Number of orders of a `k`-domain. -/
def card (k : Nat) (H : List Nat → Bool) : Nat := (orders k).countP H

/-- Orders of `H` whose swap at positions `j`, `j + 1` is again in `H`. -/
def adjAt (k j : Nat) (H : List Nat → Bool) : Nat :=
  (orders k).countP (fun M => H M && H (swapAt j M))

/-- Directed adjacent swaps of a `k`-domain. -/
def adj (k : Nat) (H : List Nat → Bool) : Nat := ((List.range (k - 1)).map (fun j => adjAt k j H)).sum

/-- `10 C(J)` for a seven-domain: weights `1, 2, 2, 2, 2, 1` on the six positions. -/
def cost10 (J : List Nat → Bool) : Nat :=
  adjAt 7 0 J + 2 * adjAt 7 1 J + 2 * adjAt 7 2 J + 2 * adjAt 7 3 J + 2 * adjAt 7 4 J + adjAt 7 5 J

/-! ### Orders of `0..k` by last and by first label -/

/-- Insert `z` last, relabelling. -/
def gB (z : Nat) (L : List Nat) : List Nat := L.map (up z) ++ [z]

/-- Insert `w` first, relabelling. -/
def gT (w : Nat) (L : List Nat) : List Nat := w :: L.map (up w)

theorem botP_eq (x : Nat) (H : List Nat → Bool) (L : List Nat) : botP x H L = H (gB x L) := rfl
theorem topP_eq (y : Nat) (H : List Nat → Bool) (L : List Nat) : topP y H L = H (gT y L) := rfl

theorem map_inj_of_inj {f : Nat → Nat} (hf : Function.Injective f) :
    ∀ {L L' : List Nat}, L.map f = L'.map f → L = L'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: L, b :: L', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf h.1, map_inj_of_inj hf h.2]

theorem gB_inj {z : Nat} {L L' : List Nat} (h : gB z L = gB z L') : L = L' := by
  unfold gB at h
  have h1 := List.append_inj_left' h rfl
  exact map_inj_of_inj (up_injective z) h1

theorem gT_inj {w : Nat} {L L' : List Nat} (h : gT w L = gT w L') : L = L' := by
  unfold gT at h
  have h1 := List.cons.inj h
  exact map_inj_of_inj (up_injective w) h1.2

/-- Duplicate-free lists with the same members are permutations of each other. -/
theorem perm_of_nodup_of_mem_iff' {α : Type} [DecidableEq α] {l₁ l₂ : List α} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  rw [h₁.count, h₂.count]
  by_cases ha : a ∈ l₁
  · rw [if_pos ha, if_pos ((h a).mp ha)]
  · rw [if_neg ha, if_neg (fun h' => ha ((h a).mpr h'))]

theorem getLast?_gB (z : Nat) (L : List Nat) : (gB z L).getLast? = some z := by
  unfold gB; simp

theorem head?_gT (w : Nat) (L : List Nat) : (gT w L).head? = some w := rfl

/-- The orders of `0..k`, listed by last label. -/
def byLast (k : Nat) : List (List Nat) := (List.range (k + 1)).flatMap (fun z => (orders k).map (gB z))

/-- The orders of `0..k`, listed by first label. -/
def byFirst (k : Nat) : List (List Nat) := (List.range (k + 1)).flatMap (fun w => (orders k).map (gT w))

theorem nodup_byLast (k : Nat) : (byLast k).Nodup := by
  unfold byLast List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun z _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (orders_nodup k).imp (fun hne e => hne (gB_inj e))
  · exact List.nodup_range.imp (fun {z₁ z₂} hne x hx y hy e => by
      obtain ⟨L, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨L', _, rfl⟩ := List.mem_map.mp hy
      have := congrArg List.getLast? e
      rw [getLast?_gB, getLast?_gB] at this
      exact hne (Option.some.inj this))

theorem nodup_byFirst (k : Nat) : (byFirst k).Nodup := by
  unfold byFirst List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun w _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (orders_nodup k).imp (fun hne e => hne (gT_inj e))
  · exact List.nodup_range.imp (fun {w₁ w₂} hne x hx y hy e => by
      obtain ⟨L, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨L', _, rfl⟩ := List.mem_map.mp hy
      have := congrArg List.head? e
      rw [head?_gT, head?_gT] at this
      exact hne (Option.some.inj this))

theorem mem_byLast {k : Nat} {M : List Nat} : M ∈ byLast k ↔ M ∈ orders (k + 1) := by
  constructor
  · intro h
    obtain ⟨z, hz, hM⟩ := List.mem_flatMap.mp h
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
    exact append_up_mem_orders (List.mem_range.mp hz) hL
  · intro h
    have hB := mem_baseB_of_mem_orders h
    unfold baseB at hB
    obtain ⟨z, hz, hM⟩ := List.mem_flatMap.mp hB
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
    exact List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨L, mem_lexOrders.mp hL, rfl⟩⟩

theorem reverse_mem_orders {n : Nat} {M : List Nat} (h : M ∈ orders n) : M.reverse ∈ orders n := by
  rw [mem_orders_iff] at h ⊢
  exact (List.reverse_perm M).trans h

theorem mem_byFirst {k : Nat} {M : List Nat} : M ∈ byFirst k ↔ M ∈ orders (k + 1) := by
  constructor
  · intro h
    obtain ⟨w, hw, hM⟩ := List.mem_flatMap.mp h
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
    exact cons_up_mem_orders (List.mem_range.mp hw) hL
  · intro h
    obtain ⟨z, hz, hM⟩ := List.mem_flatMap.mp (mem_byLast.mpr (reverse_mem_orders h))
    obtain ⟨L, hL, hLe⟩ := List.mem_map.mp hM
    have hM' : M = gT z L.reverse := by
      have := congrArg List.reverse hLe
      rw [List.reverse_reverse] at this
      rw [← this]
      unfold gB gT
      simp [List.map_reverse]
    rw [hM']
    exact List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨L.reverse, reverse_mem_orders hL, rfl⟩⟩

theorem perm_byLast (k : Nat) : (byLast k).Perm (orders (k + 1)) :=
  perm_of_nodup_of_mem_iff' (nodup_byLast k) (orders_nodup (k + 1)) (fun _ => mem_byLast)

theorem perm_byFirst (k : Nat) : (byFirst k).Perm (orders (k + 1)) :=
  perm_of_nodup_of_mem_iff' (nodup_byFirst k) (orders_nodup (k + 1)) (fun _ => mem_byFirst)

/-- **Counting by last label.** -/
theorem countP_orders_succ_last (k : Nat) (f : List Nat → Bool) :
    (orders (k + 1)).countP f = ((List.range (k + 1)).map (fun z => (orders k).countP (fun L => f (gB z L)))).sum := by
  rw [← (perm_byLast k).countP_eq, byLast, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro z _
  simp only [Function.comp, List.countP_map]
  rfl

/-- **Counting by first label.** -/
theorem countP_orders_succ_first (k : Nat) (f : List Nat → Bool) :
    (orders (k + 1)).countP f = ((List.range (k + 1)).map (fun w => (orders k).countP (fun L => f (gT w L)))).sum := by
  rw [← (perm_byFirst k).countP_eq, byFirst, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp, List.countP_map]
  rfl

/-! ### Swaps -/

theorem getD_map_of_lt {f : Nat → Nat} {L : List Nat} {i : Nat} (h : i < L.length) :
    (L.map f).getD i 0 = f (L.getD i 0) := by
  rw [getD_of_lt (by rw [List.length_map]; exact h), getD_of_lt h, List.getElem_map]

theorem swapAt_map (f : Nat → Nat) {j : Nat} {L : List Nat} (h : j + 1 < L.length) :
    swapAt j (L.map f) = (swapAt j L).map f := by
  unfold swapAt
  rw [getD_map_of_lt h, getD_map_of_lt (by omega), ← List.map_set, ← List.map_set]

theorem swapAt_append {j : Nat} {L : List Nat} (R : List Nat) (h : j + 1 < L.length) :
    swapAt j (L ++ R) = swapAt j L ++ R := by
  unfold swapAt
  have h1 : (L ++ R).getD (j + 1) 0 = L.getD (j + 1) 0 := by
    rw [getD_of_lt (by rw [List.length_append]; omega), getD_of_lt h, List.getElem_append_left h]
  have h2 : (L ++ R).getD j 0 = L.getD j 0 := by
    rw [getD_of_lt (by rw [List.length_append]; omega), getD_of_lt (by omega),
      List.getElem_append_left (by omega)]
  rw [h1, h2, List.set_append_left _ _ (by omega), List.set_append_left _ _ (by rw [List.length_set]; exact h)]

theorem swapAt_cons (a : Nat) (j : Nat) (L : List Nat) : swapAt (j + 1) (a :: L) = a :: swapAt j L := by
  unfold swapAt
  rfl

theorem length_of_mem_orders' {n : Nat} {L : List Nat} (h : L ∈ orders n) : L.length = n :=
  length_of_mem_orders h

theorem swapAt_gB (z : Nat) {j : Nat} {L : List Nat} (h : j + 1 < L.length) :
    swapAt j (gB z L) = gB z (swapAt j L) := by
  unfold gB
  rw [swapAt_append _ (by rw [List.length_map]; exact h), swapAt_map _ h]

theorem swapAt_gT (w j : Nat) (L : List Nat) (h : j + 1 < L.length) :
    swapAt (j + 1) (gT w L) = gT w (swapAt j L) := by
  unfold gT
  rw [swapAt_cons, swapAt_map _ h]

/-! ### Features over slices -/

theorem card_succ_bot (k : Nat) (H : List Nat → Bool) :
    card (k + 1) H = ((List.range (k + 1)).map (fun z => card k (botP z H))).sum := by
  unfold card
  rw [countP_orders_succ_last]
  rfl

theorem card_succ_top (k : Nat) (H : List Nat → Bool) :
    card (k + 1) H = ((List.range (k + 1)).map (fun w => card k (topP w H))).sum := by
  unfold card
  rw [countP_orders_succ_first]
  rfl

theorem adjAt_succ_bot {k j : Nat} (hj : j + 1 < k) (H : List Nat → Bool) :
    adjAt (k + 1) j H = ((List.range (k + 1)).map (fun z => adjAt k j (botP z H))).sum := by
  unfold adjAt
  rw [countP_orders_succ_last]
  congr 1
  apply List.map_congr_left
  intro z _
  apply List.countP_congr
  intro L hL
  rw [swapAt_gB z (by rw [length_of_mem_orders hL]; exact hj)]
  rfl

theorem adjAt_succ_top {k j : Nat} (hj : j + 1 < k) (H : List Nat → Bool) :
    adjAt (k + 1) (j + 1) H = ((List.range (k + 1)).map (fun w => adjAt k j (topP w H))).sum := by
  unfold adjAt
  rw [countP_orders_succ_first]
  congr 1
  apply List.map_congr_left
  intro w _
  apply List.countP_congr
  intro L hL
  rw [swapAt_gT w j L (by rw [length_of_mem_orders hL]; exact hj)]
  rfl

/-! ### Sums -/

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_comm {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Nat) :
    (l₁.map (fun a => (l₂.map (fun b => f a b)).sum)).sum = (l₂.map (fun b => (l₁.map (fun a => f a b)).sum)).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    induction l₂ with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ← ih, Nat.add_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, sum_map_add]

theorem adj_eq (k : Nat) (H : List Nat → Bool) : adj k H = ((List.range (k - 1)).map (fun j => adjAt k j H)).sum := rfl

/-- `A(H)` of a six-domain from its slices. -/
theorem adj6_split (H : List Nat → Bool) :
    adj 6 H = ((List.range 6).map (fun x => adj 5 (botP x H))).sum +
      ((List.range 6).map (fun y => adjAt 5 3 (topP y H))).sum := by
  have hb : ∀ j, j ∈ List.range 4 → adjAt 6 j H = ((List.range 6).map (fun x => adjAt 5 j (botP x H))).sum :=
    fun j hj => adjAt_succ_bot (by have := List.mem_range.mp hj; omega) H
  have ht : adjAt 6 4 H = ((List.range 6).map (fun y => adjAt 5 3 (topP y H))).sum :=
    adjAt_succ_top (k := 5) (j := 3) (by omega) H
  have e1 : adj 6 H = ((List.range 4).map (fun j => adjAt 6 j H)).sum + adjAt 6 4 H := by
    show ((List.range 5).map (fun j => adjAt 6 j H)).sum = _
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    omega
  rw [e1, ht, List.map_congr_left hb, sum_comm]
  rfl

/-- **`10 C(J)` from the six-slices.** -/
theorem cost10_split (J : List Nat → Bool) :
    cost10 J = ((List.range 7).map (fun z => adj 6 (botP z J))).sum +
      ((List.range 7).map (fun w => adj 6 (topP w J))).sum := by
  have hb : ∀ j, j ∈ List.range 5 → adjAt 7 j J = ((List.range 7).map (fun z => adjAt 6 j (botP z J))).sum :=
    fun j hj => adjAt_succ_bot (by have := List.mem_range.mp hj; omega) J
  have ht : ∀ j, j ∈ List.range 5 → adjAt 7 (j + 1) J = ((List.range 7).map (fun w => adjAt 6 j (topP w J))).sum :=
    fun j hj => adjAt_succ_top (by have := List.mem_range.mp hj; omega) J
  have e1 : ((List.range 7).map (fun z => adj 6 (botP z J))).sum = ((List.range 5).map (fun j => adjAt 7 j J)).sum := by
    rw [List.map_congr_left hb, sum_comm]
    rfl
  have e2 : ((List.range 7).map (fun w => adj 6 (topP w J))).sum = ((List.range 5).map (fun j => adjAt 7 (j + 1) J)).sum := by
    rw [List.map_congr_left ht, sum_comm]
    rfl
  rw [e1, e2]
  simp [cost10, List.range_succ]
  omega

/-! ### Relabelling invariance -/

theorem rlab_inj {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) {L L' : List Nat}
    (h : rlab σ L = rlab σ L') : L = L' := by
  rw [← rlab_pinv_rlab hσ L, h, rlab_pinv_rlab hσ L']

theorem perm_map_rlab {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) :
    ((orders n).map (rlab σ)).Perm (orders n) := by
  apply perm_of_nodup_of_mem_iff'
  · rw [List.Nodup, List.pairwise_map]
    exact (orders_nodup n).imp (fun hne e => hne (rlab_inj hσ e))
  · exact orders_nodup n
  · intro M
    constructor
    · intro h
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp h
      exact rlab_mem_orders hσ hL
    · intro h
      exact List.mem_map.mpr ⟨rlab (pinv n σ) M, rlab_mem_orders (pinv_mem_orders hσ) h, rlab_rlab_pinv hσ M⟩

theorem countP_relabel {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) (f : List Nat → Bool) :
    (orders n).countP (fun M => f (rlab σ M)) = (orders n).countP f := by
  rw [← (perm_map_rlab hσ).countP_eq f, List.countP_map]
  rfl

theorem card_relabel {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) (H : List Nat → Bool) :
    card n (fun M => H (rlab σ M)) = card n H :=
  countP_relabel hσ H

theorem rlab_swapAt {n j : Nat} {σ : List Nat} (hj : j + 1 < n) {M : List Nat} (hM : M ∈ orders n) :
    rlab σ (swapAt j M) = swapAt j (rlab σ M) := by
  rw [rlab_eq_map, rlab_eq_map, swapAt_map _ (by rw [length_of_mem_orders hM]; exact hj)]

theorem adjAt_relabel {n j : Nat} (hj : j + 1 < n) {σ : List Nat} (hσ : σ ∈ orders n) (H : List Nat → Bool) :
    adjAt n j (fun M => H (rlab σ M)) = adjAt n j H := by
  unfold adjAt
  rw [← countP_relabel hσ (fun M => H M && H (swapAt j M))]
  apply List.countP_congr
  intro M hM
  simp only [rlab_swapAt hj hM]

theorem adj_relabel {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) (H : List Nat → Bool) :
    adj n (fun M => H (rlab σ M)) = adj n H := by
  unfold adj
  congr 1
  apply List.map_congr_left
  intro j hj
  exact adjAt_relabel (by have := List.mem_range.mp hj; omega) hσ H

end CDCert.K6
