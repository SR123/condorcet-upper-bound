/-
CDCert.K6.SixSemA — what one six-level kernel check (`six_rep_k`) says, at list
level.

* `vB5`, `vT5`: the offset-free contributions read from `table5` (`0` for the empty
  slice); `sumV6 H`: their sum over the six bottom and six top five-slices of `H`;
* `ineq6_iff_sumV6`: the kernel's six-row test on the combined mask of `H` is
  `0 ≤ sumV6 H`;
* `mem_baseB_of_mem_orders`: every order of `0..k` occurs in `baseB k`;
* `rep_sound6`: if the kernel check passes for the representative mask `r`, then every
  nonempty extension `H` of `r` by a choice of `groupsPF6` satisfies `0 ≤ sumV6 H`, or
  its bottom-indexed mask is a key of `exc6`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Base12
import CDCert.K6.DfsList
import CDCert.K6.Check6
import CDCert.K6.Table5
import CDCert.K6.Check5

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000

theorem lexIdx_lexOrders5'' : (lexOrders 5).map lexIdx = List.range (lexOrders 5).length := by
  rw [length_lexOrders5']; exact lexIdx_lexOrders5

/-- Mask of a five-domain over `lexOrders 5`. -/
def m5 (p : List Nat → Bool) : Nat := maskOf (lexOrders 5) p

/-- Bottom contribution read from the table (offset removed; `0` for the empty slice). -/
noncomputable def vB5 (b : Nat) : Int :=
  if b = 0 then 0 else ((table5.find b % 2 ^ 64 : Nat) : Int) - 2 ^ 60

/-- Top contribution read from the table. -/
noncomputable def vT5 (b : Nat) : Int :=
  if b = 0 then 0 else (((table5.find b >>> 64) % 2 ^ 64 : Nat) : Int) - 2 ^ 60

/-- The six-row sum of a six-domain. -/
noncomputable def sumV6 (H : List Nat → Bool) : Int :=
  ((List.range 6).map (fun x => vB5 (m5 (botP x H)))).sum +
    ((List.range 6).map (fun y => vT5 (m5 (topP y H)))).sum

theorem bvB_eq (b : Nat) : (bvB table5 b : Int) = vB5 b + 2 ^ 60 := by
  unfold bvB vB5
  by_cases h : b = 0
  · simp [h]
  · simp only [h, if_false]
    omega

theorem bvT_eq (b : Nat) : (bvT table5 b : Int) = vT5 b + 2 ^ 60 := by
  unfold bvT vT5
  by_cases h : b = 0
  · simp [h]
  · simp only [h, if_false]
    omega

theorem sumV6_eq (H : List Nat → Bool) : sumV6 H =
    vB5 (m5 (botP 0 H)) + vB5 (m5 (botP 1 H)) + vB5 (m5 (botP 2 H)) + vB5 (m5 (botP 3 H)) +
      vB5 (m5 (botP 4 H)) + vB5 (m5 (botP 5 H)) +
    (vT5 (m5 (topP 0 H)) + vT5 (m5 (topP 1 H)) + vT5 (m5 (topP 2 H)) + vT5 (m5 (topP 3 H)) +
      vT5 (m5 (topP 4 H)) + vT5 (m5 (topP 5 H))) := by
  simp [sumV6, List.range_succ, Int.add_assoc]

/-- **The six-row test, at list level.** -/
theorem ineq6_iff_sumV6 (H : List Nat → Bool) :
    ineq6 table5 (maskOf base12 H) = true ↔ 0 ≤ sumV6 H := by
  rw [ineq6_eq_true_iff]
  have b0 : block (maskOf base12 H) 0 = m5 (botP 0 H) := block_base12_bot H (x := 0) (by decide)
  have b1 : block (maskOf base12 H) 120 = m5 (botP 1 H) := block_base12_bot H (x := 1) (by decide)
  have b2 : block (maskOf base12 H) 240 = m5 (botP 2 H) := block_base12_bot H (x := 2) (by decide)
  have b3 : block (maskOf base12 H) 360 = m5 (botP 3 H) := block_base12_bot H (x := 3) (by decide)
  have b4 : block (maskOf base12 H) 480 = m5 (botP 4 H) := block_base12_bot H (x := 4) (by decide)
  have b5 : block (maskOf base12 H) 600 = m5 (botP 5 H) := block_base12_bot H (x := 5) (by decide)
  have t0 : block (maskOf base12 H) 720 = m5 (topP 0 H) := block_base12_top H (y := 0) (by decide)
  have t1 : block (maskOf base12 H) 840 = m5 (topP 1 H) := block_base12_top H (y := 1) (by decide)
  have t2 : block (maskOf base12 H) 960 = m5 (topP 2 H) := block_base12_top H (y := 2) (by decide)
  have t3 : block (maskOf base12 H) 1080 = m5 (topP 3 H) := block_base12_top H (y := 3) (by decide)
  have t4 : block (maskOf base12 H) 1200 = m5 (topP 4 H) := block_base12_top H (y := 4) (by decide)
  have t5 : block (maskOf base12 H) 1320 = m5 (topP 5 H) := block_base12_top H (y := 5) (by decide)
  rw [b0, b1, b2, b3, b4, b5, t0, t1, t2, t3, t4, t5, sumV6_eq]
  have e0 := bvB_eq (m5 (botP 0 H)); have e1 := bvB_eq (m5 (botP 1 H))
  have e2 := bvB_eq (m5 (botP 2 H)); have e3 := bvB_eq (m5 (botP 3 H))
  have e4 := bvB_eq (m5 (botP 4 H)); have e5 := bvB_eq (m5 (botP 5 H))
  have f0 := bvT_eq (m5 (topP 0 H)); have f1 := bvT_eq (m5 (topP 1 H))
  have f2 := bvT_eq (m5 (topP 2 H)); have f3 := bvT_eq (m5 (topP 3 H))
  have f4 := bvT_eq (m5 (topP 4 H)); have f5 := bvT_eq (m5 (topP 5 H))
  omega

/-- Every order of `0..k` occurs in `baseB k`. -/
theorem mem_baseB_of_mem_orders {k : Nat} {M : List Nat} (hM : M ∈ orders (k + 1)) : M ∈ baseB k := by
  rcases List.eq_nil_or_concat M with h | ⟨M', x, hMe⟩
  · subst h
    have := (mem_of_mem_orders hM 0).mpr (by omega)
    cases this
  rw [List.concat_eq_append] at hMe
  subst hMe
  have hx : x < k + 1 := (mem_of_mem_orders hM x).mp (List.mem_append_right _ (List.mem_singleton_self x))
  have hnd := nodup_of_mem_orders hM
  have hnx : x ∉ M' := fun h => (List.nodup_append.mp hnd).2.2 x h x (List.mem_singleton_self x) rfl
  have hfilt : (M' ++ [x]).filter (fun a => a != x) = M' := by
    rw [List.filter_append]
    have : M'.filter (fun a => a != x) = M' := by
      rw [List.filter_eq_self]
      intro a ha
      have : a ≠ x := fun h => hnx (h ▸ ha)
      simpa using this
    rw [this]
    simp
  have hdel : deleteLabel x (M' ++ [x]) ∈ orders k := deleteLabel_mem_orders hx hM
  unfold baseB
  rw [List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ⟨deleteLabel x (M' ++ [x]), mem_lexOrders.mpr hdel, ?_⟩⟩
  rw [map_up_deleteLabel, hfilt]

theorem mem_base12_of_mem_orders {M : List Nat} (hM : M ∈ orders 6) : M ∈ base12 :=
  List.mem_append_left _ (mem_baseB_of_mem_orders hM)

/-- **One six-level kernel check, read off.** -/
theorem rep_sound6 {r : Nat}
    (hdfs : dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 r)) = true)
    {c : List (Opt (List Nat))} (hc : IsChoice c groupsPF6) {M0 : List Nat} (hM0 : M0 ∈ orders 6)
    (h0 : memM r (deleteLabel 5 M0) = true) (ha : allows c M0 = true) :
    0 ≤ sumV6 (fun M => memM r (deleteLabel 5 M) && allows c M) ∨
      exc6.find (maskOf (baseB 5) (fun M => memM r (deleteLabel 5 M) && allows c M)) ≠ 0 := by
  have hlift : liftOf lifts6 r = maskOf base12 (fun L => memM r (deleteLabel 5 L)) := by
    rw [lifts6_eq]
    exact liftOf_maskOf lexIdx_lexOrders5'' (deleteLabel 5)
      (fun L hL => mem_lexOrders.mpr (deleteLabel_mem_orders (by omega) (mem_base12 hL))) r
  rw [hlift, groups6_eq] at hdfs
  obtain ⟨e, he, hdec⟩ := dfs_sound_list _ base12 groupsPF6 _ hdfs c hc
    ⟨M0, mem_base12_of_mem_orders hM0, h0, ha⟩
  rw [leafOK6_eq_true_iff, hdec, ineq6_iff_sumV6, maskOf_base12_mod] at he
  exact he

end CDCert.K6
