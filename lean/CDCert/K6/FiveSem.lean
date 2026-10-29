/-
CDCert.K6.FiveSem — **five-level coverage**: every nonempty five-label domain of
`groupsEP 5` is a relabelling of one of the 1160 five-type representatives.

* `iso_of_relabel_mask`: a kernel-checked relabelling row turns a mask equality into
  "`p L = memM r (rlab σ L)` for every order `L`";
* `four_classify` (from `five_F4`): every nonempty `groupsEP 4` domain is a relabelling
  of one of the 45 four-type representatives;
* `five_extend_of` (from `five_F5_all`): every nonempty extension of a four-type
  representative by the options introduced with label 4 is a relabelling of a
  five-type representative;
* `five_cover`: the combination, through `allows_choiceEPN_relabel`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.DfsList
import CDCert.K6.Relabel
import CDCert.K6.Check5
import CDCert.K6.Five.F4
import CDCert.K6.Five.F5All

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000

theorem rlab_injective {n : Nat} {σ : List Nat} (hσ : σ ∈ orders n) {L L' : List Nat}
    (h : rlab σ L = rlab σ L') : L = L' := by
  rw [← rlab_pinv_rlab hσ L, h, rlab_pinv_rlab hσ L']

/-- A relabelling row of `σ` maps the mask of `p` to `r`: read off order by order. -/
theorem iso_of_relabel_mask {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length) {n : Nat}
    (hPo : ∀ L, L ∈ P ↔ L ∈ orders n) {σ : List Nat} (hσ : σ ∈ orders n) {p : List Nat → Bool}
    {r : Nat} (h : relabelI (P.map (fun L => lexIdx (rlab σ L))) (maskOf P p) = r) :
    ∀ L, L ∈ orders n → p L = memM r (rlab σ L) := by
  have hσP : ∀ L, L ∈ P → rlab σ L ∈ P := fun L hL =>
    (hPo _).mpr (rlab_mem_orders hσ ((hPo L).mp hL))
  rw [relabelI_maskOf' hP σ hσP p] at h
  intro L hL
  have hM : rlab σ L ∈ P := hσP L ((hPo L).mpr hL)
  have := memM_of_maskOf_eq hP h hM
  rw [← this]
  cases hp : p L
  · symm
    apply decide_eq_false
    rintro ⟨L', _, hL', heq⟩
    have := rlab_injective hσ heq
    subst this
    rw [hp] at hL'
    cases hL'
  · symm
    apply decide_eq_true
    exact ⟨L, (hPo L).mpr hL, hp, rfl⟩

theorem length_lexOrders4 : (lexOrders 4).length = 24 := by decide
theorem length_lexOrders5 : (lexOrders 5).length = 120 := by decide

theorem lexIdx_lexOrders4' : (lexOrders 4).map lexIdx = List.range (lexOrders 4).length := by
  rw [length_lexOrders4]; exact lexIdx_lexOrders4

theorem lexIdx_lexOrders5' : (lexOrders 5).map lexIdx = List.range (lexOrders 5).length := by
  rw [length_lexOrders5]; exact lexIdx_lexOrders5

theorem getL_rows4 {t : Nat} (ht : t < 24) :
    ∃ σ, σ ∈ orders 4 ∧ getL rows4 t = (lexOrders 4).map (fun L => lexIdx (rlab σ L)) := by
  have hl : t < (lexOrders 4).length := by rw [length_lexOrders4]; exact ht
  refine ⟨(lexOrders 4)[t], mem_lexOrders.mp (List.getElem_mem hl), ?_⟩
  rw [getL_eq, rows4_eq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
  rfl

theorem getL_rows5 {t : Nat} (ht : t < 120) :
    ∃ σ, σ ∈ orders 5 ∧ getL rows5 t = (lexOrders 5).map (fun L => lexIdx (rlab σ L)) := by
  have hl : t < (lexOrders 5).length := by rw [length_lexOrders5]; exact ht
  refine ⟨(lexOrders 5)[t], mem_lexOrders.mp (List.getElem_mem hl), ?_⟩
  rw [getL_eq, rows5_eq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
  rfl

theorem full4_eq : (nat_lit 0xffffff) = maskOf (lexOrders 4) (fun _ => true) := by decide

/-- **Four-level classification.** -/
theorem four_classify {c : List (Opt (List Nat))} (hc : IsChoice c (groupsEP 4)) {L0 : List Nat}
    (hL0 : L0 ∈ orders 4) (ha : allows c L0 = true) :
    ∃ σ, σ ∈ orders 4 ∧ ∃ j, j < 45 ∧ ∀ L, L ∈ orders 4 → allows c L = memM (rep4T.find j) (rlab σ L) := by
  have h := five_F4
  rw [groups4_eq, full4_eq] at h
  obtain ⟨e, he, hdec⟩ := dfs_sound_list _ (lexOrders 4) (groupsEP 4) (fun _ => true) h c hc
    ⟨L0, mem_lexOrders.mpr hL0, rfl, ha⟩
  obtain ⟨t, j, ht, hj, hrel⟩ := leafW_sound he
  obtain ⟨σ, hσ, hrow⟩ := getL_rows4 ht
  rw [hrow, hdec] at hrel
  refine ⟨σ, hσ, j, hj, ?_⟩
  intro L hL
  have := iso_of_relabel_mask lexIdx_lexOrders4' (fun L => mem_lexOrders) hσ hrel L hL
  simpa using this

/-- **Extensions of a four-type representative.** -/
theorem five_extend_of {r4 : Nat}
    (h5 : dfs1 (leafW rows5 120 1160 hint5 rep5T) groups5n (enc (liftOf lifts5 r4)) = true)
    {c : List (Opt (List Nat))} (hc : IsChoice c groupsPF5) {L0 : List Nat} (hL0 : L0 ∈ orders 5)
    (hm : memM r4 (deleteLabel 4 L0) = true) (ha : allows c L0 = true) :
    ∃ τ, τ ∈ orders 5 ∧ ∃ k, k < 1160 ∧ ∀ L, L ∈ orders 5 →
      (memM r4 (deleteLabel 4 L) && allows c L) = memM (rep5T.find k) (rlab τ L) := by
  have hlift : liftOf lifts5 r4 = maskOf (lexOrders 5) (fun L => memM r4 (deleteLabel 4 L)) := by
    rw [lifts5_eq]
    exact liftOf_maskOf lexIdx_lexOrders4' (deleteLabel 4)
      (fun L hL => mem_lexOrders.mpr (deleteLabel_mem_orders (by omega) (mem_lexOrders.mp hL))) r4
  rw [hlift, groups5n_eq] at h5
  obtain ⟨e, he, hdec⟩ := dfs_sound_list _ (lexOrders 5) groupsPF5 _ h5 c hc
    ⟨L0, mem_lexOrders.mpr hL0, hm, ha⟩
  obtain ⟨t, k, ht, hk, hrel⟩ := leafW_sound he
  obtain ⟨τ, hτ, hrow⟩ := getL_rows5 ht
  rw [hrow, hdec] at hrel
  exact ⟨τ, hτ, k, hk, iso_of_relabel_mask lexIdx_lexOrders5' (fun L => mem_lexOrders) hτ hrel⟩

theorem rep4T_mem {j : Nat} (hj : j < 45) : rep4T.find j ∈ reps4 := by
  have h := rep4T_eq
  have hl : j < ((List.range 45).map rep4T.find).length := by simp; exact hj
  have := List.getElem_mem hl
  rw [List.getElem_map, List.getElem_range, h] at this
  exact this

/-- The groups introduced with label 4 of `choiceNew`, pairs first. -/
def choicePF (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool) (k : Nat) :
    List (Opt (List Nat)) :=
  (List.range k).map (fun a => pairChoice a k (pairN a k)) ++
  (newTriples k).map (fun t => holdsL t.1 t.2.1 t.2.2 (lawN t))

theorem allows_choicePF (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool)
    (k : Nat) (M : List Nat) : allows (choicePF lawN pairN k) M = allows (choiceNew lawN pairN k) M := by
  unfold choicePF choiceNew
  rw [allows_append, allows_append, Bool.and_comm]

theorem isChoice_choicePF5 {lawN : Nat × Nat × Nat → Fin 3 × Fin 3} (hlaw : ∀ t, lawN t ∈ lawsExtreme)
    (pairN : Nat → Nat → Option Bool) : IsChoice (choicePF lawN pairN 4) groupsPF5 :=
  isChoice_append.mpr ⟨_, _, rfl,
    isChoice_map_map _ _ _ (fun a _ => pairChoice_mem a 4 _),
    isChoice_map_map _ _ _ (fun t _ => List.mem_map_of_mem (hlaw t))⟩

/-- Permutations of `0..m-1` preserve `{a | a < n}` for `n ≥ m`. -/
theorem lt_iff_app {m n : Nat} {σ : List Nat} (hσ : σ ∈ orders m) (hmn : m ≤ n) (a : Nat) :
    a < n ↔ app σ a < n := by
  by_cases ha : a < m
  · have := app_lt hσ ha
    constructor <;> intro _ <;> omega
  · rw [app_of_ge hσ (by omega)]

theorem allows_local_restrict {k : Nat} {c : List (Opt (List Nat))} (hc : IsChoice c (groupsEP k))
    (L : List Nat) : allows c L = allows c (restrictTo k L) :=
  (allows_restrictTo (isChoice_local (local_groupsEP k) hc) L).symm

/-- Extend a permutation of `0..k-1` by fixing `k`. -/
theorem append_mem_orders {k : Nat} {σ : List Nat} (hσ : σ ∈ orders k) : σ ++ [k] ∈ orders (k + 1) := by
  rw [mem_orders_iff] at hσ ⊢
  rw [List.range_succ]
  exact hσ.append_right [k]

theorem app_append {k : Nat} {σ : List Nat} (hσ : σ ∈ orders k) (a : Nat) : app (σ ++ [k]) a = app σ a := by
  have h1 := append_mem_orders hσ
  by_cases ha : a < k
  · rw [app_of_lt hσ ha, app_of_lt h1 (by omega)]
    simp [List.getElem_append_left (by rw [length_of_mem_orders hσ]; exact ha)]
  · by_cases hak : a = k
    · subst hak
      rw [app_of_ge hσ (Nat.le_refl _), app_of_lt h1 (by omega)]
      have hl := length_of_mem_orders hσ
      rw [List.getElem_append_right (by omega)]
      simp [hl]
    · rw [app_of_ge hσ (by omega), app_of_ge h1 (by omega)]

theorem rlab_append {k : Nat} {σ : List Nat} (hσ : σ ∈ orders k) (L : List Nat) :
    rlab (σ ++ [k]) L = rlab σ L := by
  rw [rlab_eq_map, rlab_eq_map]
  exact List.map_congr_left (fun a _ => app_append hσ a)

/-- **Five-level coverage.** -/
theorem five_cover {c : List (Opt (List Nat))} (hc : IsChoice c (groupsEP 5)) {L0 : List Nat}
    (hL0 : L0 ∈ orders 5) (ha : allows c L0 = true) :
    ∃ ρ, ρ ∈ orders 5 ∧ ∃ k, k < 1160 ∧ ∀ L, L ∈ orders 5 → allows c L = memM (rep5T.find k) (rlab ρ L) := by
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff 5 c hc
  have hOld : IsChoice (choiceEPN lawN pairN 4) (groupsEP 4) :=
    isChoice_choiceEPN lawN pairN 4 (fun _ t _ _ => hlaw t)
  -- the old domain is nonempty
  have hsplit : ∀ M, allows (choiceEPN lawN pairN 5) M =
      (allows (choiceEPN lawN pairN 4) M && allows (choiceNew lawN pairN 4) M) := fun M =>
    allows_append _ _ M
  have hL04 : restrictTo 4 L0 ∈ orders 4 := restrictTo_mem_orders hL0
  have ha4 : allows (choiceEPN lawN pairN 4) (restrictTo 4 L0) = true := by
    rw [← allows_local_restrict hOld, ]
    rw [hsplit, Bool.and_eq_true] at ha
    exact ha.1
  obtain ⟨σ, hσ, j, hj, hiso4⟩ := four_classify hOld hL04 ha4
  -- transport the laws by σ
  have hfg : ∀ a, app σ (app (pinv 4 σ) a) = a := app_app_pinv hσ
  have hgf : ∀ a, app (pinv 4 σ) (app σ a) = a := app_pinv_app hσ
  have hpinv := pinv_mem_orders hσ
  have hn4 := lt_iff_app hpinv (Nat.le_refl 4)
  have hn5 := lt_iff_app hpinv (by omega : 4 ≤ 5)
  have hlaw' : ∀ t, lawT (app σ) (app (pinv 4 σ)) lawN t ∈ lawsExtreme := lawT_extreme hlaw
  have hOld' : IsChoice (choiceEPN (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 4)
      (groupsEP 4) := isChoice_choiceEPN _ _ 4 (fun _ t _ _ => hlaw' t)
  -- the relabelled old domain is the representative
  have hrep4 : ∀ M, M ∈ orders 4 →
      allows (choiceEPN (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 4) M =
        memM (rep4T.find j) M := by
    intro M hM
    rw [allows_choiceEPN_relabel hfg hgf hn4 lawN pairN hM]
    have hMg : M.map (app (pinv 4 σ)) ∈ orders 4 := map_mem_orders hfg hgf hn4 hM
    rw [hiso4 _ hMg]
    congr 1
    show rlab σ (rlab (pinv 4 σ) M) = M
    exact rlab_rlab_pinv hσ M
  -- the relabelled five-domain, with new options pairs first
  have hrel5 : ∀ M, M ∈ orders 5 → allows (choiceEPN lawN pairN 5) (M.map (app (pinv 4 σ))) =
      (memM (rep4T.find j) (deleteLabel 4 M) &&
        allows (choicePF (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 4) M) := by
    intro M hM
    rw [← allows_choiceEPN_relabel hfg hgf hn5 lawN pairN hM]
    rw [show choiceEPN (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 5 =
      choiceEPN (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 4 ++
        choiceNew (lawT (app σ) (app (pinv 4 σ)) lawN) (pairT (app (pinv 4 σ)) pairN) 4 from rfl]
    rw [allows_append, allows_choicePF, allows_local_restrict hOld' M,
      hrep4 _ (restrictTo_mem_orders hM), restrictTo_eq_deleteLabel hM]
  -- a witness order for the extension
  have hM0 : rlab σ L0 ∈ orders 5 := by
    rw [← rlab_append hσ]; exact rlab_mem_orders (append_mem_orders hσ) hL0
  have hback : (rlab σ L0).map (app (pinv 4 σ)) = L0 := rlab_pinv_rlab hσ L0
  have hw := hrel5 _ hM0
  rw [hback, ha] at hw
  have hw' := hw.symm
  rw [Bool.and_eq_true] at hw'
  obtain ⟨τ, hτ, k, hk, hiso5⟩ := five_extend_of (five_F5_all _ (rep4T_mem hj))
    (isChoice_choicePF5 hlaw' _) hM0 hw'.1 hw'.2
  -- compose
  have hσ5 := append_mem_orders hσ
  refine ⟨(σ ++ [4]).map (app τ), comp_mem_orders hτ hσ5, k, hk, ?_⟩
  intro L hL
  have hML : rlab σ L ∈ orders 5 := by rw [← rlab_append hσ]; exact rlab_mem_orders hσ5 hL
  have e1 : allows (choiceEPN lawN pairN 5) L =
      allows (choiceEPN lawN pairN 5) ((rlab σ L).map (app (pinv 4 σ))) := by
    rw [show (rlab σ L).map (app (pinv 4 σ)) = rlab (pinv 4 σ) (rlab σ L) from rfl, rlab_pinv_rlab hσ L]
  rw [e1, hrel5 _ hML, hiso5 _ hML, ← rlab_comp hτ hσ5, rlab_append hσ]

end CDCert.K6
