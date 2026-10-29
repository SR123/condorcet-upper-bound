/-
CDCert.K6.SumInv — relabelling invariance of the six-row sum, given relabelling
invariance of the five-table on five-label domains (`TabInv`, proved from the
kernel checks `T2` and the five-level coverage in `CDCert.K6.TabSem`).

* `perm_sum_int`: sums of integer lists are invariant under permutation;
* `m5_eq_zero_iff`: the mask of a five-domain is `0` iff it is empty;
* `vB5_relabel`, `vT5_relabel`: relabelling a five-domain or empty slice does not
  change its table contributions;
* `sumV6_relabel`: relabelling a six-label domain does not change `sumV6`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.SixSemA

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

theorem perm_sum_int {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Relabelling invariance of the five-table on five-label domains. -/
def TabInv : Prop :=
  ∀ (p : List Nat → Bool), IsDom 5 p → ∀ σ, σ ∈ orders 5 →
    table5.find (m5 (fun L => p (rlab σ L))) = table5.find (m5 p)

theorem m5_eq_zero_iff (p : List Nat → Bool) : m5 p = 0 ↔ IsEmptyOn 5 p := by
  unfold m5
  have h0 : (0 : Nat) = maskOf (lexOrders 5) (fun _ => false) := by
    induction (lexOrders 5) with
    | nil => rfl
    | cons _ _ ih => simp [maskOf, ← ih]
  rw [h0, maskOf_eq_iff]
  constructor
  · intro h L hL
    exact h L (mem_lexOrders.mpr hL)
  · intro h L hL
    exact h L (mem_lexOrders.mp hL)

theorem m5_congr {p q : List Nat → Bool} (h : ∀ L, L ∈ orders 5 → p L = q L) : m5 p = m5 q := by
  unfold m5
  rw [maskOf_eq_iff]
  intro L hL
  exact h L (mem_lexOrders.mp hL)

theorem isEmptyOn_relabel_iff {p : List Nat → Bool} {σ : List Nat} (hσ : σ ∈ orders 5) :
    IsEmptyOn 5 (fun L => p (rlab σ L)) ↔ IsEmptyOn 5 p := by
  constructor
  · intro h L hL
    have := h (rlab (pinv 5 σ) L) (rlab_mem_orders (pinv_mem_orders hσ) hL)
    simp only at this
    rwa [rlab_rlab_pinv hσ] at this
  · intro h L hL
    exact h _ (rlab_mem_orders hσ hL)

theorem vB5_relabel (hT : TabInv) {p : List Nat → Bool} (hp : IsDom 5 p ∨ IsEmptyOn 5 p)
    {σ : List Nat} (hσ : σ ∈ orders 5) : vB5 (m5 (fun L => p (rlab σ L))) = vB5 (m5 p) := by
  unfold vB5
  have hz : m5 (fun L => p (rlab σ L)) = 0 ↔ m5 p = 0 := by
    rw [m5_eq_zero_iff, m5_eq_zero_iff, isEmptyOn_relabel_iff hσ]
  by_cases h0 : m5 p = 0
  · rw [if_pos h0, if_pos (hz.mpr h0)]
  · rw [if_neg h0, if_neg (fun h => h0 (hz.mp h))]
    rcases hp with hp | hp
    · rw [hT p hp σ hσ]
    · exact absurd ((m5_eq_zero_iff p).mpr hp) h0

theorem vT5_relabel (hT : TabInv) {p : List Nat → Bool} (hp : IsDom 5 p ∨ IsEmptyOn 5 p)
    {σ : List Nat} (hσ : σ ∈ orders 5) : vT5 (m5 (fun L => p (rlab σ L))) = vT5 (m5 p) := by
  unfold vT5
  have hz : m5 (fun L => p (rlab σ L)) = 0 ↔ m5 p = 0 := by
    rw [m5_eq_zero_iff, m5_eq_zero_iff, isEmptyOn_relabel_iff hσ]
  by_cases h0 : m5 p = 0
  · rw [if_pos h0, if_pos (hz.mpr h0)]
  · rw [if_neg h0, if_neg (fun h => h0 (hz.mp h))]
    rcases hp with hp | hp
    · rw [hT p hp σ hσ]
    · exact absurd ((m5_eq_zero_iff p).mpr hp) h0

/-- Reindexing a sum over `range n` by a permutation. -/
theorem sum_range_perm {n : Nat} {π : List Nat} (hπ : π ∈ orders n) (f : Nat → Int) :
    ((List.range n).map (fun x => f (app π x))).sum = ((List.range n).map f).sum := by
  have h1 : (List.range n).map (fun x => f (app π x)) = π.map f := by
    have : (List.range n).map (app π) = π := by
      apply List.ext_getElem
      · rw [List.length_map, List.length_range, length_of_mem_orders hπ]
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_range]
        rw [List.length_map, List.length_range] at h1
        rw [app_of_lt hπ h1]
    calc (List.range n).map (fun x => f (app π x)) = ((List.range n).map (app π)).map f := by
          rw [List.map_map]; rfl
      _ = π.map f := by rw [this]
  rw [h1]
  exact perm_sum_int ((mem_orders_iff.mp hπ).map f)

/-- **The six-row sum is invariant under relabelling.** -/
theorem sumV6_relabel (hT : TabInv) {H : List Nat → Bool} (hH : IsDom 6 H) {π : List Nat}
    (hπ : π ∈ orders 6) : sumV6 (fun M => H (rlab π M)) = sumV6 H := by
  unfold sumV6
  have hb : ∀ x, x ∈ List.range 6 → vB5 (m5 (botP x (fun M => H (rlab π M)))) =
      vB5 (m5 (botP (app π x) H)) := by
    intro x hx
    have hx' := List.mem_range.mp hx
    rw [m5_congr (fun L hL => botP_relabel hπ hx' H hL)]
    exact vB5_relabel hT (slice_bot (app_lt hπ hx') hH) (slicePerm_mem hπ hx')
  have ht : ∀ y, y ∈ List.range 6 → vT5 (m5 (topP y (fun M => H (rlab π M)))) =
      vT5 (m5 (topP (app π y) H)) := by
    intro y hy
    have hy' := List.mem_range.mp hy
    rw [m5_congr (fun L hL => topP_relabel hπ hy' H hL)]
    exact vT5_relabel hT (slice_top (app_lt hπ hy') hH) (slicePerm_mem hπ hy')
  rw [List.map_congr_left hb, List.map_congr_left ht,
    sum_range_perm hπ (fun x => vB5 (m5 (botP x H))), sum_range_perm hπ (fun y => vT5 (m5 (topP y H)))]

end CDCert.K6
