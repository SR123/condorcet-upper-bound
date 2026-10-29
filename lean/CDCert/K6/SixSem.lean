/-
CDCert.K6.SixSem — **the six-level finite fact** for every six-label domain of
`groupsEP 6`: it is a relabelling of one of the exceptional six-types met by the check
(`excIdx`: T types 9–13 and S types 4, 5, 8), or its six-row sum is nonnegative:

  `six_sem : IsDom 6 H → (∃ j ∈ excIdx, IsoM (excRep6.getD j 0) H) ∨ 0 ≤ sumV6 H`.

From the kernel checks: the 48 six-level files (`six_all`), the five-level coverage
(`five_cover`), relabelling invariance of the table (`tabInv`) and the witnesses for the
204 failing masks (`exc6_iso`).

* `memB6 m`: the six-domain with bottom-indexed mask `m` (bit `idxB M`);
* `IsoM m H`: `H` is a relabelling of `memB6 m`;
* `iso_of_relabel_maskB`: a relabelling row over `baseB 5` turns a mask equality into `IsoM`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Six.All
import CDCert.K6.TabSem
import CDCert.K6.Tab.ExcIso
import CDCert.K6.Theta

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

theorem idxB_baseB' : (baseB 5).map idxB = List.range (baseB 5).length := by
  rw [length_baseB5]; exact idxB_baseB

theorem mem_baseB5_iff {M : List Nat} : M ∈ baseB 5 ↔ M ∈ orders 6 :=
  ⟨mem_baseB, mem_baseB_of_mem_orders⟩

/-- Reading a mask over `baseB 5`. -/
theorem memB6_of_maskOf_eq {p : List Nat → Bool} {m : Nat} (h : maskOf (baseB 5) p = m) {M : List Nat}
    (hM : M ∈ baseB 5) : p M = memB6 m M := by
  obtain ⟨hlt, heq⟩ := getElem_ix idxB_baseB' hM
  have := congrArg (fun x => Nat.testBit x (idxB M)) h
  simp only [testBit_maskOf, List.getElem?_eq_getElem hlt, heq] at this
  exact this

/-- **A relabelling row over `baseB 5` gives an isomorphism.** -/
theorem iso_of_relabel_maskB {σ : List Nat} (hσ : σ ∈ orders 6) {p : List Nat → Bool} {m : Nat}
    (h : relabelI ((baseB 5).map (fun M => idxB (rlab σ M))) (maskOf (baseB 5) p) = m) :
    ∀ M, M ∈ orders 6 → p M = memB6 m (rlab σ M) := by
  have hσP : ∀ L, L ∈ baseB 5 → rlab σ L ∈ baseB 5 := fun L hL =>
    mem_baseB5_iff.mpr (rlab_mem_orders hσ (mem_baseB5_iff.mp hL))
  rw [relabelI_maskOf_ix idxB_baseB' σ hσP p] at h
  intro M hM
  have hM' : rlab σ M ∈ baseB 5 := hσP M (mem_baseB5_iff.mpr hM)
  have := memB6_of_maskOf_eq h hM'
  rw [← this]
  cases hp : p M
  · symm
    apply decide_eq_false
    rintro ⟨L', _, hL', heq⟩
    have := rlab_inj hσ heq
    subst this
    rw [hp] at hL'
    cases hL'
  · symm
    apply decide_eq_true
    exact ⟨M, mem_baseB5_iff.mpr hM, hp, rfl⟩

theorem isoM_of_relabel {m : Nat} {H : List Nat → Bool} {π : List Nat} (hπ : π ∈ orders 6)
    (h : IsoM m (fun M => H (rlab π M))) : IsoM m H := by
  obtain ⟨τ, hτ, hτm⟩ := h
  have hpi := pinv_mem_orders hπ
  refine ⟨(pinv 6 π).map (app τ), comp_mem_orders hτ hpi, ?_⟩
  intro M hM
  have := hτm (rlab (pinv 6 π) M) (rlab_mem_orders hpi hM)
  simp only at this
  rw [rlab_rlab_pinv hπ] at this
  rw [this, rlab_comp hτ hpi]

/-! ### Sums of empty and of agreeing domains -/

theorem sumV6_congr {H H' : List Nat → Bool} (h : ∀ M, M ∈ orders 6 → H M = H' M) : sumV6 H = sumV6 H' := by
  unfold sumV6
  have hb : ∀ x, x ∈ List.range 6 → vB5 (m5 (botP x H)) = vB5 (m5 (botP x H')) := by
    intro x hx
    rw [m5_congr (p := botP x H) (q := botP x H') (fun L hL => h _ (append_up_mem_orders (List.mem_range.mp hx) hL))]
  have ht : ∀ y, y ∈ List.range 6 → vT5 (m5 (topP y H)) = vT5 (m5 (topP y H')) := by
    intro y hy
    rw [m5_congr (p := topP y H) (q := topP y H') (fun L hL => h _ (cons_up_mem_orders (List.mem_range.mp hy) hL))]
  rw [List.map_congr_left hb, List.map_congr_left ht]

theorem sumV6_empty {H : List Nat → Bool} (h : IsEmptyOn 6 H) : sumV6 H = 0 := by
  have h0 : ∀ M, M ∈ orders 6 → H M = (fun _ => false) M := fun M hM => h M hM
  rw [sumV6_congr h0]
  have hb : ∀ x, m5 (botP x (fun _ => false)) = 0 := fun x => (m5_eq_zero_iff _).mpr (fun _ _ => rfl)
  have ht : ∀ y, m5 (topP y (fun _ => false)) = 0 := fun y => (m5_eq_zero_iff _).mpr (fun _ _ => rfl)
  have e1 : ∀ x, x ∈ List.range 6 → vB5 (m5 (botP x (fun _ => false))) = 0 := fun x _ => by
    rw [hb]; rfl
  have e2 : ∀ y, y ∈ List.range 6 → vT5 (m5 (topP y (fun _ => false))) = 0 := fun y _ => by
    rw [ht]; rfl
  unfold sumV6
  rw [List.map_congr_left e1, List.map_congr_left e2]
  rfl

/-! ### The extension structure at label 5 -/

theorem isChoice_choicePF6 {lawN : Nat × Nat × Nat → Fin 3 × Fin 3} (hlaw : ∀ t, lawN t ∈ lawsExtreme)
    (pairN : Nat → Nat → Option Bool) : IsChoice (choicePF lawN pairN 5) groupsPF6 :=
  isChoice_append.mpr ⟨_, _, rfl,
    isChoice_map_map _ _ _ (fun a _ => pairChoice_mem a 5 _),
    isChoice_map_map _ _ _ (fun t _ => List.mem_map_of_mem (hlaw t))⟩

theorem exc6_mem_keys {m : Nat} (h : exc6.find m ≠ 0) : m ∈ exc6keys := by
  have h1 := KTree.mem_keys_of_find_ne_zero exc6 m h
  have h2 : exc6.keys = exc6keys := exc6_keys
  rw [h2] at h1
  exact h1

/-- **The six-level finite fact.** -/
theorem six_sem {H : List Nat → Bool} (hH : IsDom 6 H) :
    (∃ j, j ∈ excIdx ∧ IsoM (excRep6.getD j 0) H) ∨ 0 ≤ sumV6 H := by
  by_cases hE : IsEmptyOn 6 H
  · right; rw [sumV6_empty hE]; exact Int.le_refl 0
  have : ∃ M0, M0 ∈ orders 6 ∧ H M0 = true := by
    apply Classical.byContradiction
    intro hno
    apply hE
    intro L hL
    cases h : H L
    · rfl
    · exact absurd ⟨L, hL, h⟩ hno
  obtain ⟨M0, hM0, hH0⟩ := this
  have hHdom := hH
  obtain ⟨c, hc, hHc⟩ := hH
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff 6 c hc
  have hOld : IsChoice (choiceEPN lawN pairN 5) (groupsEP 5) :=
    isChoice_choiceEPN lawN pairN 5 (fun _ t _ _ => hlaw t)
  have hsplit : ∀ M, allows (choiceEPN lawN pairN 6) M =
      (allows (choiceEPN lawN pairN 5) M && allows (choiceNew lawN pairN 5) M) := fun M =>
    allows_append _ _ M
  have hL05 : restrictTo 5 M0 ∈ orders 5 := restrictTo_mem_orders hM0
  have ha5 : allows (choiceEPN lawN pairN 5) (restrictTo 5 M0) = true := by
    rw [← allows_local_restrict hOld]
    have h1 := hHc M0 hM0
    rw [hH0, hsplit] at h1
    exact (Bool.and_eq_true _ _ ▸ h1.symm).1
  obtain ⟨σ, hσ, k, hk, hiso5⟩ := five_cover hOld hL05 ha5
  -- transport the laws by σ
  have hfg : ∀ a, app σ (app (pinv 5 σ) a) = a := app_app_pinv hσ
  have hgf : ∀ a, app (pinv 5 σ) (app σ a) = a := app_pinv_app hσ
  have hpinv := pinv_mem_orders hσ
  have hn5 := lt_iff_app hpinv (Nat.le_refl 5)
  have hn6 := lt_iff_app hpinv (by omega : 5 ≤ 6)
  have hlaw' : ∀ t, lawT (app σ) (app (pinv 5 σ)) lawN t ∈ lawsExtreme := lawT_extreme hlaw
  have hOld' : IsChoice (choiceEPN (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5)
      (groupsEP 5) := isChoice_choiceEPN _ _ 5 (fun _ t _ _ => hlaw' t)
  have hrep5 : ∀ M, M ∈ orders 5 →
      allows (choiceEPN (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5) M =
        memM (rep5T.find k) M := by
    intro M hM
    rw [allows_choiceEPN_relabel hfg hgf hn5 lawN pairN hM]
    have hMg : M.map (app (pinv 5 σ)) ∈ orders 5 := map_mem_orders hfg hgf hn5 hM
    rw [hiso5 _ hMg]
    congr 1
    show rlab σ (rlab (pinv 5 σ) M) = M
    exact rlab_rlab_pinv hσ M
  have hrel6 : ∀ M, M ∈ orders 6 → allows (choiceEPN lawN pairN 6) (M.map (app (pinv 5 σ))) =
      (memM (rep5T.find k) (deleteLabel 5 M) &&
        allows (choicePF (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5) M) := by
    intro M hM
    rw [← allows_choiceEPN_relabel hfg hgf hn6 lawN pairN hM]
    rw [show choiceEPN (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 6 =
      choiceEPN (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5 ++
        choiceNew (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5 from rfl]
    rw [allows_append, allows_choicePF, allows_local_restrict hOld' M,
      hrep5 _ (restrictTo_mem_orders hM), restrictTo_eq_deleteLabel hM]
  -- the relabelled domain is an extension of the representative
  have hσ6 := append_mem_orders hσ
  have hπ := append_mem_orders hpinv
  have hM0' : rlab σ M0 ∈ orders 6 := by rw [← rlab_append hσ]; exact rlab_mem_orders hσ6 hM0
  have hback : (rlab σ M0).map (app (pinv 5 σ)) = M0 := rlab_pinv_rlab hσ M0
  have hw := hrel6 _ hM0'
  rw [hback, ← hHc M0 hM0, hH0] at hw
  have hw' := hw.symm
  rw [Bool.and_eq_true] at hw'
  have hdfs := six_all _ (rep5T_mem hk)
  have hres := rep_sound6 hdfs (isChoice_choicePF6 hlaw' _) hM0' hw'.1 hw'.2
  -- `H'` is `H` relabelled by `π = pinv σ ++ [5]`
  have hH' : ∀ M, M ∈ orders 6 →
      (memM (rep5T.find k) (deleteLabel 5 M) &&
        allows (choicePF (lawT (app σ) (app (pinv 5 σ)) lawN) (pairT (app (pinv 5 σ)) pairN) 5) M) =
      (fun M => allows (choiceEPN lawN pairN 6) M) (rlab (pinv 5 σ ++ [5]) M) := by
    intro M hM
    rw [← hrel6 M hM, rlab_append hpinv]
    rfl
  have hHπ : IsDom 6 (fun M => allows (choiceEPN lawN pairN 6) (rlab (pinv 5 σ ++ [5]) M)) := by
    have hd : IsDom 6 (fun M => allows (choiceEPN lawN pairN 6) M) :=
      ⟨choiceEPN lawN pairN 6, hc, fun _ _ => rfl⟩
    exact isDom_relabel hd hπ
  have hdom6 : IsDom 6 (fun M => allows (choiceEPN lawN pairN 6) M) :=
    ⟨choiceEPN lawN pairN 6, hc, fun _ _ => rfl⟩
  rcases hres with hs | hx
  · right
    rw [sumV6_congr hH', sumV6_relabel tabInv hdom6 hπ] at hs
    rw [sumV6_congr hHc]
    exact hs
  · left
    obtain ⟨τ, hτ, j, hj, hrow⟩ := exc6_iso _ (exc6_mem_keys hx)
    have hiso := iso_of_relabel_maskB hτ hrow
    refine ⟨j, hj, ?_⟩
    have h1 : IsoM (excRep6.getD j 0) (fun M => allows (choiceEPN lawN pairN 6) (rlab (pinv 5 σ ++ [5]) M)) :=
      ⟨τ, hτ, fun M hM => by rw [← hH' M hM]; exact hiso M hM⟩
    obtain ⟨τ', hτ', hτm⟩ := isoM_of_relabel hπ h1
    exact ⟨τ', hτ', fun M hM => by rw [hHc M hM]; exact hτm M hM⟩

end CDCert.K6
