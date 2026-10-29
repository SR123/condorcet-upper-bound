/-
CDCert.K6.R8 — **the receiver argument**: if no six-slice of a seven-domain `J` is a
relabelling of an exceptional type other than `R₈`, then `Λ(J) ≥ η|J|`
(`lam_receiver`; scaled by `2D`: `2ηD|J| ≤ lamD J`).

* per slice: `θ_b(H) ≥ η|H|/2 + 4η r_t(H) − 4η[H ≅ R₈]` and the top analogue
  (`thB_bound`, `thT_bound`): from the six-level fact (`six_sem`, `sumV6_eq_sD`) outside
  `T ∪ S`, and `θ_b = θ_t = 0`, `|H| = 8`, `r_b = r_t = 0` on `R₈` (`r8_facts`);
* counting (`count_bot`, `count_top`): every bottom `R₈` slice `B_z J` has a top five-slice
  of type 866 (`R₈` with its first alternative deleted), which is a bottom five-slice of a
  top slice of `J` (`topP_botP`), so `Σ_w r_b(T_w J) ≥ #{z : B_z J ≅ R₈}`; symmetrically
  `Σ_z r_t(B_z J) ≥ #{w : T_w J ≅ R₈}` with type 41.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.ThetaInv
import CDCert.K6.SixSem
import CDCert.K6.Seven.Keys2

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-- The mask of `R₈`. -/
noncomputable def r8 : Nat := excRep6.getD 9 0

/-- `[H ≅ R₈]`. -/
noncomputable def isR8 (H : List Nat → Bool) : Nat := @ite _ (IsoM r8 H) (Classical.propDecidable _) 1 0

theorem card_of_isoM {m : Nat} {H : List Nat → Bool} (h : IsoM m H) : card 6 H = card 6 (memB6 m) := by
  obtain ⟨ρ, hρ, hρm⟩ := isoM_inv h
  rw [card_congr hρm, card_relabel hρ]

/-- **Facts about the slices isomorphic to `R₈`.** -/
theorem r8_facts {H : List Nat → Bool} (hH : DomE 6 H) (h : IsoM r8 H) :
    card 6 H = 8 ∧ sD H = 0 ∧ rb H = 0 ∧ rt H = 0 ∧ ¬ IsS H := by
  obtain ⟨ρ, hρ, hρm⟩ := isoM_inv h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_of_isoM h]; exact r8_card
  · rw [← sD_relabel hH hρ, ← sD_congr hρm]; exact r8_sD
  · rw [← rb_relabel hH hρ, ← rb_congr hρm]; exact r8_rb
  · rw [← rt_relabel hH hρ, ← rt_congr hρm]; exact r8_rt
  · rintro ⟨i, hi, hiso⟩
    have e1 := key6_of_isoM hH hiso
    have e2 := key6_of_isoM hH h
    have h1 := sKeys_mem i hi
    rw [e1, ← e2] at h1
    exact h1 r8_notS

theorem pD_notS {H : List Nat → Bool} (h : ¬ IsS H) : pD H = 4 * (cE : Int) * ((rt H : Int) - rb H) := by
  unfold pD; rw [if_neg h]

theorem r8_th {H : List Nat → Bool} (hH : DomE 6 H) (h : IsoM r8 H) : thB H = 0 ∧ thT H = 0 := by
  obtain ⟨_, h2, h3, h4, h5⟩ := r8_facts hH h
  have hp : pD H = 0 := by rw [pD_notS h5, h3, h4]; simp
  unfold thB thT
  rw [h2, hp]
  exact ⟨rfl, rfl⟩

/-! ### Empty slices -/

theorem empty_notIso {H : List Nat → Bool} (hE : IsEmptyOn 6 H) {j : Nat} (hj : j < 14) :
    ¬ IsoM (excRep6.getD j 0) H := by
  intro h
  have := card_of_isoM h
  rw [(card_eq_zero_iff H).mpr hE] at this
  exact exc_card_pos j hj this.symm

theorem empty_notS {H : List Nat → Bool} (hE : IsEmptyOn 6 H) : ¬ IsS H := by
  rintro ⟨i, hi, h⟩
  exact empty_notIso hE (by omega) h

theorem potW_empty {p : List Nat → Bool} (h : IsEmptyOn 5 p) : potW p = 0 := by
  unfold potW; rw [(card_eq_zero_iff p).mpr h]; simp

theorem isTy_empty (k : Nat) {p : List Nat → Bool} (h : IsEmptyOn 5 p) : isTy k p = 0 := by
  unfold isTy; rw [if_neg (fun h' => h'.1 ((card_eq_zero_iff p).mpr h))]

theorem isum_zero {α : Type} (l : List α) (f : α → Int) (h : ∀ x, x ∈ l → f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem nsum_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x, x ∈ l → f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem empty_facts {H : List Nat → Bool} (hE : IsEmptyOn 6 H) :
    card 6 H = 0 ∧ rb H = 0 ∧ rt H = 0 ∧ thB H = 0 ∧ thT H = 0 := by
  have hbE : ∀ x, x < 6 → IsEmptyOn 5 (botP x H) := fun x hx L hL => hE _ (append_up_mem_orders hx hL)
  have htE : ∀ y, y < 6 → IsEmptyOn 5 (topP y H) := fun y hy L hL => hE _ (cons_up_mem_orders hy hL)
  have hc : card 6 H = 0 := (card_eq_zero_iff H).mpr hE
  have hrb : rb H = 0 := nsum_zero _ _ (fun x hx => isTy_empty 866 (hbE x (List.mem_range.mp hx)))
  have hrt : rt H = 0 := nsum_zero _ _ (fun y hy => isTy_empty 41 (htE y (List.mem_range.mp hy)))
  have hb : bD H = 0 := isum_zero _ _ (fun x hx => potW_empty (hbE x (List.mem_range.mp hx)))
  have ht : tD H = 0 := isum_zero _ _ (fun y hy => potW_empty (htE y (List.mem_range.mp hy)))
  have hs : sD H = 0 := by unfold sD; rw [hc, adj_empty hE, hb, ht]; simp
  have hp : pD H = 0 := by rw [pD_notS (empty_notS hE), hrb, hrt]; simp
  refine ⟨hc, hrb, hrt, ?_, ?_⟩
  · unfold thB; rw [hs, hp]; rfl
  · unfold thT; rw [hs, hp]; rfl

/-! ### The per-slice bounds -/

theorem excIdx_lt {j : Nat} (hj : j ∈ excIdx) : j < 14 := by
  simp only [excIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
  omega

/-- No exceptional type other than `R₈`. -/
def NoExc (H : List Nat → Bool) : Prop := ∀ j, j < 14 → j ≠ 9 → ¬ IsoM (excRep6.getD j 0) H

theorem notS_of_noExc {H : List Nat → Bool} (h : NoExc H) : ¬ IsS H := by
  rintro ⟨i, hi, hiso⟩
  exact h i (by omega) (by omega) hiso

/-- The six-level fact outside `T ∪ S`: the receiver slack. -/
theorem receiver_slack {H : List Nat → Bool} (hH : IsDom 6 H) (hno : NoExc H) (hr : ¬ IsoM r8 H) :
    (cE : Int) * (card 6 H + 4 * rb H + 4 * rt H) ≤ sD H := by
  rcases six_sem hH with ⟨j, hj, hiso⟩ | hs
  · by_cases h9 : j = 9
    · subst h9; exact absurd hiso hr
    · exact absurd hiso (hno j (excIdx_lt hj) h9)
  · rw [sumV6_eq_sD hH] at hs
    omega

theorem thB_bound {H : List Nat → Bool} (hH : DomE 6 H) (hno : NoExc H) :
    (cE : Int) * card 6 H + 8 * cE * rt H - 8 * cE * isR8 H ≤ thB H := by
  rcases hH with hH | hE
  · by_cases hr : IsoM r8 H
    · obtain ⟨h1, _, _, h4, _⟩ := r8_facts (Or.inl hH) hr
      have hth := (r8_th (Or.inl hH) hr).1
      have : isR8 H = 1 := by unfold isR8; rw [if_pos hr]
      rw [this, h1, h4, hth]
      have hE : (cE : Int) = 58198140 := rfl
      rw [hE]; omega
    · have : isR8 H = 0 := by unfold isR8; rw [if_neg hr]
      have hs := receiver_slack hH hno hr
      unfold thB
      rw [this, pD_notS (notS_of_noExc hno)]
      have hE : (cE : Int) = 58198140 := rfl
      rw [hE] at hs ⊢
      omega
  · obtain ⟨h1, _, h3, h4, _⟩ := empty_facts hE
    have : isR8 H = 0 := by unfold isR8; rw [if_neg (show ¬ IsoM r8 H from empty_notIso (j := 9) hE (by omega))]
    rw [this, h1, h3, h4]
    simp

theorem thT_bound {H : List Nat → Bool} (hH : DomE 6 H) (hno : NoExc H) :
    (cE : Int) * card 6 H + 8 * cE * rb H - 8 * cE * isR8 H ≤ thT H := by
  rcases hH with hH | hE
  · by_cases hr : IsoM r8 H
    · obtain ⟨h1, _, h3, _, _⟩ := r8_facts (Or.inl hH) hr
      have hth := (r8_th (Or.inl hH) hr).2
      have : isR8 H = 1 := by unfold isR8; rw [if_pos hr]
      rw [this, h1, h3, hth]
      have hE : (cE : Int) = 58198140 := rfl
      rw [hE]; omega
    · have : isR8 H = 0 := by unfold isR8; rw [if_neg hr]
      have hs := receiver_slack hH hno hr
      unfold thT
      rw [this, pD_notS (notS_of_noExc hno)]
      have hE : (cE : Int) = 58198140 := rfl
      rw [hE] at hs ⊢
      omega
  · obtain ⟨h1, h2, _, _, h5⟩ := empty_facts hE
    have : isR8 H = 0 := by unfold isR8; rw [if_neg (show ¬ IsoM r8 H from empty_notIso (j := 9) hE (by omega))]
    rw [this, h1, h2, h5]
    simp

/-! ### Counting the receivers -/

theorem isum_le {α : Type} (l : List α) (f g : α → Int) (h : ∀ x, x ∈ l → f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem isum_single_le {l : List Nat} {a : Nat} (ha : a ∈ l) (f : Nat → Int) (hf : ∀ x, x ∈ l → 0 ≤ f x) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := hf b (List.mem_cons_self)
    have hl : 0 ≤ (l.map f).sum := by
      have := isum_le l (fun _ => 0) f (fun x hx => hf x (List.mem_cons_of_mem _ hx))
      rw [isum_zero l (fun _ => (0 : Int)) (fun _ _ => rfl)] at this
      exact this
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih ha (fun x hx => hf x (List.mem_cons_of_mem _ hx))
      omega

/-- Double sums over slices of slices, reindexed (`topP_botP`). -/
theorem sum_double_slice (F : (List Nat → Bool) → Int) (J : List Nat → Bool) :
    ((List.range 7).map (fun z => ((List.range 6).map (fun y => F (topP y (botP z J)))).sum)).sum =
      ((List.range 7).map (fun w => ((List.range 6).map (fun x => F (botP x (topP w J)))).sum)).sum := by
  rw [isum_pairs76 (fun z y => F (topP y (botP z J))), isum_pairs76 (fun w x => F (botP x (topP w J)))]
  simp only [topP_botP]
  have := perm_sum_int (perm_pairs76.map (fun p => F (botP p.2 (topP p.1 J))))
  rw [List.map_map] at this
  exact this

theorem isTy_le_one (k : Nat) (p : List Nat → Bool) : isTy k p ≤ 1 := by
  unfold isTy; split <;> omega

/-- A slice isomorphic to `R₈` has a top five-slice of type 866 and a bottom one of type 41. -/
theorem r8_slices {H : List Nat → Bool} (hH : DomE 6 H) (h : IsoM r8 H) :
    (∃ a, a < 6 ∧ isTy 866 (topP a H) = 1) ∧ (∃ b, b < 6 ∧ isTy 41 (botP b H) = 1) := by
  obtain ⟨σ, hσ, hσm⟩ := h
  have hpi := pinv_mem_orders hσ
  constructor
  · refine ⟨app (pinv 6 σ) 0, app_lt hpi (by omega), ?_⟩
    have ha := app_lt hpi (show 0 < 6 by omega)
    have hτ := slicePerm_mem hσ ha
    have hτi := pinv_mem_orders hτ
    -- `topP a H` is a relabelling of `topP 0 R₈`
    have e : ∀ L, L ∈ orders 5 → topP (app (pinv 6 σ) 0) H L =
        topP 0 (memB6 r8) (rlab (slicePerm 5 (app (pinv 6 σ) 0) σ) L) := by
      intro L hL
      have h1 := topP_relabel hσ ha (memB6 r8) hL
      rw [app_app_pinv hσ] at h1
      rw [← h1]
      exact hσm _ (cons_up_mem_orders ha hL)
    have hd := domE_top ha hH
    have e2 : ∀ L, L ∈ orders 5 → (fun L => topP (app (pinv 6 σ) 0) H (rlab (pinv 5 (slicePerm 5 (app (pinv 6 σ) 0) σ)) L)) L =
        topP 0 (memB6 r8) L := by
      intro L hL
      simp only
      rw [e _ (rlab_mem_orders hτi hL), rlab_rlab_pinv hτ]
    rw [← isTy_relabel 866 hd hτi, isTy_congr 866 e2]
    exact r8_top866
  · refine ⟨app (pinv 6 σ) 5, app_lt hpi (by omega), ?_⟩
    have hb := app_lt hpi (show 5 < 6 by omega)
    have hτ := slicePerm_mem hσ hb
    have hτi := pinv_mem_orders hτ
    have e : ∀ L, L ∈ orders 5 → botP (app (pinv 6 σ) 5) H L =
        botP 5 (memB6 r8) (rlab (slicePerm 5 (app (pinv 6 σ) 5) σ) L) := by
      intro L hL
      have h1 := botP_relabel hσ hb (memB6 r8) hL
      rw [app_app_pinv hσ] at h1
      rw [← h1]
      exact hσm _ (append_up_mem_orders hb hL)
    have hd := domE_bot hb hH
    have e2 : ∀ L, L ∈ orders 5 → (fun L => botP (app (pinv 6 σ) 5) H (rlab (pinv 5 (slicePerm 5 (app (pinv 6 σ) 5) σ)) L)) L =
        botP 5 (memB6 r8) L := by
      intro L hL
      simp only
      rw [e _ (rlab_mem_orders hτi hL), rlab_rlab_pinv hτ]
    rw [← isTy_relabel 41 hd hτi, isTy_congr 41 e2]
    exact r8_bot41

theorem isR8_le {H : List Nat → Bool} (hH : DomE 6 H) :
    (isR8 H : Int) ≤ ((List.range 6).map (fun y => (isTy 866 (topP y H) : Int))).sum ∧
    (isR8 H : Int) ≤ ((List.range 6).map (fun x => (isTy 41 (botP x H) : Int))).sum := by
  by_cases hr : IsoM r8 H
  · have h1 : isR8 H = 1 := by unfold isR8; rw [if_pos hr]
    obtain ⟨⟨a, ha, ha1⟩, ⟨b, hb, hb1⟩⟩ := r8_slices hH hr
    rw [h1]
    constructor
    · have := isum_single_le (List.mem_range.mpr ha) (fun y => (isTy 866 (topP y H) : Int)) (fun _ _ => Int.natCast_nonneg _)
      simp only [ha1] at this
      exact this
    · have := isum_single_le (List.mem_range.mpr hb) (fun x => (isTy 41 (botP x H) : Int)) (fun _ _ => Int.natCast_nonneg _)
      simp only [hb1] at this
      exact this
  · have h0 : isR8 H = 0 := by unfold isR8; rw [if_neg hr]
    rw [h0]
    constructor
    · have := isum_le (List.range 6) (fun _ => (0 : Int)) (fun y => (isTy 866 (topP y H) : Int)) (fun _ _ => Int.natCast_nonneg _)
      rw [isum_zero _ (fun _ => (0 : Int)) (fun _ _ => rfl)] at this
      exact this
    · have := isum_le (List.range 6) (fun _ => (0 : Int)) (fun x => (isTy 41 (botP x H) : Int)) (fun _ _ => Int.natCast_nonneg _)
      rw [isum_zero _ (fun _ => (0 : Int)) (fun _ _ => rfl)] at this
      exact this

/-- **Bottom `R₈` slices are paid by their receivers.** -/
theorem count_bot {J : List Nat → Bool} (hJ : DomE 7 J) :
    ((List.range 7).map (fun z => (isR8 (botP z J) : Int))).sum ≤ ((List.range 7).map (fun w => (rb (topP w J) : Int))).sum := by
  have e : ((List.range 7).map (fun w => (rb (topP w J) : Int))).sum =
      ((List.range 7).map (fun z => ((List.range 6).map (fun y => (isTy 866 (topP y (botP z J)) : Int))).sum)).sum := by
    rw [sum_double_slice (fun p => (isTy 866 p : Int)) J]
    exact congrArg List.sum (List.map_congr_left (fun w _ => rb_cast _))
  rw [e]
  exact isum_le _ _ _ (fun z hz => (isR8_le (domE_bot (List.mem_range.mp hz) hJ)).1)

/-- **Top `R₈` slices are paid by their receivers.** -/
theorem count_top {J : List Nat → Bool} (hJ : DomE 7 J) :
    ((List.range 7).map (fun w => (isR8 (topP w J) : Int))).sum ≤ ((List.range 7).map (fun z => (rt (botP z J) : Int))).sum := by
  have e : ((List.range 7).map (fun z => (rt (botP z J) : Int))).sum =
      ((List.range 7).map (fun w => ((List.range 6).map (fun x => (isTy 41 (botP x (topP w J)) : Int))).sum)).sum := by
    rw [← sum_double_slice (fun p => (isTy 41 p : Int)) J]
    exact congrArg List.sum (List.map_congr_left (fun z _ => rt_cast _))
  rw [e]
  exact isum_le _ _ _ (fun w hw => (isR8_le (domE_top (List.mem_range.mp hw) hJ)).2)

/-- **The receiver argument.** -/
theorem lam_receiver {J : List Nat → Bool} (hJ : DomE 7 J)
    (hb : ∀ z, z < 7 → NoExc (botP z J)) (ht : ∀ w, w < 7 → NoExc (topP w J)) :
    2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hB : ((List.range 7).map (fun z => (cE : Int) * card 6 (botP z J) + 8 * cE * rt (botP z J) -
      8 * cE * isR8 (botP z J))).sum ≤ ((List.range 7).map (fun z => thB (botP z J))).sum :=
    isum_le _ _ _ (fun z hz => thB_bound (domE_bot (List.mem_range.mp hz) hJ) (hb z (List.mem_range.mp hz)))
  have hT : ((List.range 7).map (fun w => (cE : Int) * card 6 (topP w J) + 8 * cE * rb (topP w J) -
      8 * cE * isR8 (topP w J))).sum ≤ ((List.range 7).map (fun w => thT (topP w J))).sum :=
    isum_le _ _ _ (fun w hw => thT_bound (domE_top (List.mem_range.mp hw) hJ) (ht w (List.mem_range.mp hw)))
  have cb := count_bot hJ
  have ct := count_top hJ
  have hcb : ((List.range 7).map (fun z => (card 6 (botP z J) : Int))).sum = card 7 J := by
    rw [isum_cast, ← card_succ_bot]
  have hct : ((List.range 7).map (fun w => (card 6 (topP w J) : Int))).sum = card 7 J := by
    rw [isum_cast, ← card_succ_top]
  rw [isum_map_sub, isum_map_add, isum_map_mul, isum_map_mul, isum_map_mul, hcb] at hB
  rw [isum_map_sub, isum_map_add, isum_map_mul, isum_map_mul, isum_map_mul, hct] at hT
  unfold lamD
  have hE : (cE : Int) = 58198140 := rfl
  rw [hE] at hB hT ⊢
  omega

end CDCert.K6
