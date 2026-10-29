/-
CDCert.K6.ThetaInv — invariance of the potential under relabelling, and dependence on
the values on orders only.

For five-domains (`DomE 5`): `ty5`, `potW`, `isTy`. For six-domains (`DomE 6`): `bD`, `tD`,
`rb`, `rt`, `sD`, `key6`, `IsS`, `sIdx` (unique, by the distinct S keys), `pD`, `thB`, `thT`,
`qD`. For seven-domains (`IsDom 7`): `lamD`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.ThetaSem

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Slices of domains-or-empty -/

theorem domE_bot {k x : Nat} (hx : x < k + 1) {H : List Nat → Bool} (hH : DomE (k + 1) H) : DomE k (botP x H) := by
  rcases hH with hH | hH
  · exact slice_bot hx hH
  · exact Or.inr (fun L hL => hH _ (append_up_mem_orders hx hL))

theorem domE_top {k y : Nat} (hy : y < k + 1) {H : List Nat → Bool} (hH : DomE (k + 1) H) : DomE k (topP y H) := by
  rcases hH with hH | hH
  · exact slice_top hy hH
  · exact Or.inr (fun L hL => hH _ (cons_up_mem_orders hy hL))

/-! ### Five-domains -/

theorem m5_relabel_zero {p : List Nat → Bool} {σ : List Nat} (hσ : σ ∈ orders 5) :
    m5 (fun L => p (rlab σ L)) = 0 ↔ m5 p = 0 := by
  rw [m5_eq_zero_iff, m5_eq_zero_iff, isEmptyOn_relabel_iff hσ]

theorem find_m5_relabel {p : List Nat → Bool} (hp : DomE 5 p) {σ : List Nat} (hσ : σ ∈ orders 5) :
    table5.find (m5 (fun L => p (rlab σ L))) = table5.find (m5 p) := by
  rcases hp with hp | hp
  · exact tabInv p hp σ hσ
  · have h1 : m5 p = 0 := (m5_eq_zero_iff p).mpr hp
    rw [h1, (m5_relabel_zero hσ).mpr h1]

theorem ty5_relabel' {p : List Nat → Bool} (hp : DomE 5 p) {σ : List Nat} (hσ : σ ∈ orders 5) :
    ty5 (fun L => p (rlab σ L)) = ty5 p := by
  unfold ty5; rw [find_m5_relabel hp hσ]

theorem potW_relabel {p : List Nat → Bool} (hp : DomE 5 p) {σ : List Nat} (hσ : σ ∈ orders 5) :
    potW (fun L => p (rlab σ L)) = potW p := by
  unfold potW; rw [card_relabel hσ, ty5_relabel' hp hσ]

theorem isTy_relabel (k : Nat) {p : List Nat → Bool} (hp : DomE 5 p) {σ : List Nat} (hσ : σ ∈ orders 5) :
    isTy k (fun L => p (rlab σ L)) = isTy k p := by
  unfold isTy; rw [card_relabel hσ, ty5_relabel' hp hσ]

theorem potW_congr {p q : List Nat → Bool} (h : ∀ L, L ∈ orders 5 → p L = q L) : potW p = potW q := by
  unfold potW; rw [card_congr h, ty5_congr h]

theorem isTy_congr (k : Nat) {p q : List Nat → Bool} (h : ∀ L, L ∈ orders 5 → p L = q L) : isTy k p = isTy k q := by
  unfold isTy; rw [card_congr h, ty5_congr h]

/-- Functions of five-domains that the relabelling invariance applies to. -/
def Inv5 (F : (List Nat → Bool) → Int) : Prop :=
  (∀ p, DomE 5 p → ∀ σ, σ ∈ orders 5 → F (fun L => p (rlab σ L)) = F p) ∧
  (∀ p q, (∀ L, L ∈ orders 5 → p L = q L) → F p = F q)

theorem inv5_potW : Inv5 potW := ⟨fun _ hp _ hσ => potW_relabel hp hσ, fun _ _ h => potW_congr h⟩

theorem inv5_isTy (k : Nat) : Inv5 (fun p => (isTy k p : Int)) :=
  ⟨fun _ hp _ hσ => by simp only [isTy_relabel k hp hσ], fun _ _ h => by simp only [isTy_congr k h]⟩

theorem inv5_tab {f : Nat → Nat} (hf : ∃ (c : Nat) (G : Nat → Nat), ∀ b, f b = if b = 0 then c else G (table5.find b)) :
    Inv5 (fun p => (f (m5 p) : Int)) := by
  obtain ⟨c, G, hfe⟩ := hf
  refine ⟨fun p hp σ hσ => ?_, fun p q h => by simp only [m5_congr h]⟩
  simp only [hfe]
  by_cases h0 : m5 p = 0
  · rw [if_pos h0, if_pos ((m5_relabel_zero hσ).mpr h0)]
  · rw [if_neg h0, if_neg (fun h' => h0 ((m5_relabel_zero hσ).mp h')), find_m5_relabel hp hσ]

/-! ### Sums over the slices of six-domains -/

theorem bsum_relabel {F : (List Nat → Bool) → Int} (hF : Inv5 F) {H : List Nat → Bool} (hH : DomE 6 H)
    {π : List Nat} (hπ : π ∈ orders 6) :
    ((List.range 6).map (fun x => F (botP x (fun M => H (rlab π M))))).sum =
      ((List.range 6).map (fun x => F (botP x H))).sum := by
  have hb : ∀ x, x ∈ List.range 6 → F (botP x (fun M => H (rlab π M))) = F (botP (app π x) H) := by
    intro x hx
    have hx' := List.mem_range.mp hx
    rw [hF.2 _ _ (fun L hL => botP_relabel hπ hx' H hL)]
    exact hF.1 _ (domE_bot (app_lt hπ hx') hH) _ (slicePerm_mem hπ hx')
  rw [List.map_congr_left hb, sum_range_perm hπ (fun x => F (botP x H))]

theorem tsum_relabel {F : (List Nat → Bool) → Int} (hF : Inv5 F) {H : List Nat → Bool} (hH : DomE 6 H)
    {π : List Nat} (hπ : π ∈ orders 6) :
    ((List.range 6).map (fun y => F (topP y (fun M => H (rlab π M))))).sum =
      ((List.range 6).map (fun y => F (topP y H))).sum := by
  have hb : ∀ y, y ∈ List.range 6 → F (topP y (fun M => H (rlab π M))) = F (topP (app π y) H) := by
    intro y hy
    have hy' := List.mem_range.mp hy
    rw [hF.2 _ _ (fun L hL => topP_relabel hπ hy' H hL)]
    exact hF.1 _ (domE_top (app_lt hπ hy') hH) _ (slicePerm_mem hπ hy')
  rw [List.map_congr_left hb, sum_range_perm hπ (fun y => F (topP y H))]

theorem bsum_congr {F : (List Nat → Bool) → Int} (hF : Inv5 F) {H H' : List Nat → Bool}
    (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    ((List.range 6).map (fun x => F (botP x H))).sum = ((List.range 6).map (fun x => F (botP x H'))).sum := by
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hF.2 _ _ (fun L hL => h _ (append_up_mem_orders (List.mem_range.mp hx) hL))

theorem tsum_congr {F : (List Nat → Bool) → Int} (hF : Inv5 F) {H H' : List Nat → Bool}
    (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    ((List.range 6).map (fun y => F (topP y H))).sum = ((List.range 6).map (fun y => F (topP y H'))).sum := by
  congr 1
  apply List.map_congr_left
  intro y hy
  exact hF.2 _ _ (fun L hL => h _ (cons_up_mem_orders (List.mem_range.mp hy) hL))

theorem rb_cast (H : List Nat → Bool) : (rb H : Int) = ((List.range 6).map (fun x => (isTy 866 (botP x H) : Int))).sum := by
  unfold rb; rw [isum_cast]

theorem rt_cast (H : List Nat → Bool) : (rt H : Int) = ((List.range 6).map (fun y => (isTy 41 (topP y H) : Int))).sum := by
  unfold rt; rw [isum_cast]

section Six
variable {H H' : List Nat → Bool} {π : List Nat}

theorem bD_relabel (hH : DomE 6 H) (hπ : π ∈ orders 6) : bD (fun M => H (rlab π M)) = bD H :=
  bsum_relabel inv5_potW hH hπ
theorem tD_relabel (hH : DomE 6 H) (hπ : π ∈ orders 6) : tD (fun M => H (rlab π M)) = tD H :=
  tsum_relabel inv5_potW hH hπ
theorem rb_relabel (hH : DomE 6 H) (hπ : π ∈ orders 6) : rb (fun M => H (rlab π M)) = rb H := by
  have := bsum_relabel (inv5_isTy 866) hH hπ
  rw [← rb_cast, ← rb_cast] at this
  exact Int.ofNat.inj this
theorem rt_relabel (hH : DomE 6 H) (hπ : π ∈ orders 6) : rt (fun M => H (rlab π M)) = rt H := by
  have := tsum_relabel (inv5_isTy 41) hH hπ
  rw [← rt_cast, ← rt_cast] at this
  exact Int.ofNat.inj this
theorem sD_relabel (hH : DomE 6 H) (hπ : π ∈ orders 6) : sD (fun M => H (rlab π M)) = sD H := by
  unfold sD; rw [card_relabel hπ, adj_relabel hπ, bD_relabel hH hπ, tD_relabel hH hπ]

theorem bD_congr (h : ∀ M, M ∈ orders 6 → H M = H' M) : bD H = bD H' := bsum_congr inv5_potW h
theorem tD_congr (h : ∀ M, M ∈ orders 6 → H M = H' M) : tD H = tD H' := tsum_congr inv5_potW h
theorem rb_congr (h : ∀ M, M ∈ orders 6 → H M = H' M) : rb H = rb H' := by
  have := bsum_congr (inv5_isTy 866) h
  rw [← rb_cast, ← rb_cast] at this
  exact Int.ofNat.inj this
theorem rt_congr (h : ∀ M, M ∈ orders 6 → H M = H' M) : rt H = rt H' := by
  have := tsum_congr (inv5_isTy 41) h
  rw [← rt_cast, ← rt_cast] at this
  exact Int.ofNat.inj this
theorem sD_congr (h : ∀ M, M ∈ orders 6 → H M = H' M) : sD H = sD H' := by
  unfold sD; rw [card_congr h, adj_congr h, bD_congr h, tD_congr h]

end Six

/-! ### The key -/

theorem sumOff_eq (f : Nat → Nat) (m : Nat) (os : List Nat) :
    sumOff f m os = (os.map (fun o => f (blk120 m o))).sum := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    show Nat.add (f (blk120 m o)) (sumOff f m os) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem blk120_eq (m o : Nat) : blk120 m o = block m o := by
  unfold blk120 block
  rw [land_m120]
  rfl

theorem oB12_eq : oB12 = (List.range 6).map (fun x => 120 * x) := by decide
theorem oT12_eq : oT12 = (List.range 6).map (fun y => 720 + 120 * y) := by decide

theorem sumOff_oB12 (f : Nat → Nat) (H : List Nat → Bool) :
    sumOff f (maskOf base12 H) oB12 = ((List.range 6).map (fun x => f (m5 (botP x H)))).sum := by
  rw [sumOff_eq, oB12_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp, blk120_eq]
  rw [block_base12_bot H (List.mem_range.mp hx)]
  rfl

theorem sumOff_oT12 (f : Nat → Nat) (H : List Nat → Bool) :
    sumOff f (maskOf base12 H) oT12 = ((List.range 6).map (fun y => f (m5 (topP y H)))).sum := by
  rw [sumOff_eq, oT12_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro y hy
  simp only [Function.comp, blk120_eq]
  rw [block_base12_top H (List.mem_range.mp hy)]
  rfl

theorem natsum_cast_eq {l : List Nat} {f g : Nat → Nat}
    (h : ((l.map (fun x => (f x : Int))).sum) = ((l.map (fun x => (g x : Int))).sum)) :
    (l.map f).sum = (l.map g).sum := by
  rw [isum_cast, isum_cast] at h
  exact Int.ofNat.inj h

/-- The key, through the slices. -/
theorem key6_eq (H : List Nat → Bool) : key6 H =
    Nat.add ((List.range 6).map (fun x => cB table5 (m5 (botP x H)))).sum
    (Nat.add (Nat.shiftLeft ((List.range 6).map (fun y => cT table5 (m5 (topP y H)))).sum 70)
    (Nat.add (Nat.shiftLeft ((List.range 6).map (fun x => cCard table5 (m5 (botP x H)))).sum 140)
    (Nat.add (Nat.shiftLeft ((List.range 6).map (fun x => c866 table5 (m5 (botP x H)))).sum 150)
    (Nat.add (Nat.shiftLeft ((List.range 6).map (fun y => c41 table5 (m5 (topP y H)))).sum 155)
    (Nat.add (Nat.shiftLeft ((List.range 6).map (fun x => cA5 table5 (m5 (botP x H)))).sum 160)
      (Nat.shiftLeft ((List.range 6).map (fun y => cA53 table5 (m5 (topP y H)))).sum 175)))))) := by
  unfold key6 sKey
  simp only [sumOff_oB12, sumOff_oT12]

theorem tabFn_cB : ∃ (c : Nat) (G : Nat → Nat), ∀ b, cB table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => v % 2 ^ 64, cB_eq table5⟩
theorem tabFn_cT : ∃ (c : Nat) (G : Nat → Nat), ∀ b, cT table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => (v >>> 64) % 2 ^ 64, cT_eq table5⟩
theorem tabFn_cCard : ∃ (c : Nat) (G : Nat → Nat), ∀ b, cCard table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => (v >>> 128) % 256, cCard_eq table5⟩
theorem tabFn_cA5 : ∃ (c : Nat) (G : Nat → Nat), ∀ b, cA5 table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => (v >>> 136) % 1024, cA5_eq table5⟩
theorem tabFn_cA53 : ∃ (c : Nat) (G : Nat → Nat), ∀ b, cA53 table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => (v >>> 146) % 256, cA53_eq table5⟩
theorem tabFn_c866 : ∃ (c : Nat) (G : Nat → Nat), ∀ b, c866 table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => if v >>> 154 = 866 then 1 else 0, c866_eq table5⟩
theorem tabFn_c41 : ∃ (c : Nat) (G : Nat → Nat), ∀ b, c41 table5 b = if b = 0 then c else G (table5.find b) :=
  ⟨_, fun v => if v >>> 154 = 41 then 1 else 0, c41_eq table5⟩

theorem key6_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    key6 (fun M => H (rlab π M)) = key6 H := by
  rw [key6_eq, key6_eq]
  rw [natsum_cast_eq (bsum_relabel (inv5_tab tabFn_cB) hH hπ),
    natsum_cast_eq (tsum_relabel (inv5_tab tabFn_cT) hH hπ),
    natsum_cast_eq (bsum_relabel (inv5_tab tabFn_cCard) hH hπ),
    natsum_cast_eq (bsum_relabel (inv5_tab tabFn_c866) hH hπ),
    natsum_cast_eq (tsum_relabel (inv5_tab tabFn_c41) hH hπ),
    natsum_cast_eq (bsum_relabel (inv5_tab tabFn_cA5) hH hπ),
    natsum_cast_eq (tsum_relabel (inv5_tab tabFn_cA53) hH hπ)]

theorem key6_congr {H H' : List Nat → Bool} (h : ∀ M, M ∈ orders 6 → H M = H' M) : key6 H = key6 H' := by
  rw [key6_eq, key6_eq]
  rw [natsum_cast_eq (bsum_congr (inv5_tab tabFn_cB) h), natsum_cast_eq (tsum_congr (inv5_tab tabFn_cT) h),
    natsum_cast_eq (bsum_congr (inv5_tab tabFn_cCard) h), natsum_cast_eq (bsum_congr (inv5_tab tabFn_c866) h),
    natsum_cast_eq (tsum_congr (inv5_tab tabFn_c41) h), natsum_cast_eq (bsum_congr (inv5_tab tabFn_cA5) h),
    natsum_cast_eq (tsum_congr (inv5_tab tabFn_cA53) h)]

/-! ### Isomorphism types -/

theorem isoM_relabel_iff {m : Nat} {H : List Nat → Bool} {π : List Nat} (hπ : π ∈ orders 6) :
    IsoM m (fun M => H (rlab π M)) ↔ IsoM m H := by
  constructor
  · rintro ⟨τ, hτ, hτm⟩
    have hpi := pinv_mem_orders hπ
    refine ⟨(pinv 6 π).map (app τ), comp_mem_orders hτ hpi, ?_⟩
    intro M hM
    have := hτm (rlab (pinv 6 π) M) (rlab_mem_orders hpi hM)
    simp only at this
    rw [rlab_rlab_pinv hπ] at this
    rw [this, rlab_comp hτ hpi]
  · rintro ⟨τ, hτ, hτm⟩
    refine ⟨π.map (app τ), comp_mem_orders hτ hπ, ?_⟩
    intro M hM
    simp only
    rw [hτm _ (rlab_mem_orders hπ hM), rlab_comp hτ hπ]

theorem isoM_congr {m : Nat} {H H' : List Nat → Bool} (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    IsoM m H ↔ IsoM m H' := by
  constructor
  · rintro ⟨τ, hτ, hτm⟩; exact ⟨τ, hτ, fun M hM => (h M hM).symm.trans (hτm M hM)⟩
  · rintro ⟨τ, hτ, hτm⟩; exact ⟨τ, hτ, fun M hM => (h M hM).trans (hτm M hM)⟩

/-- A relabelling of the domain with mask `m` agrees with it on orders. -/
theorem isoM_inv {m : Nat} {H : List Nat → Bool} (h : IsoM m H) :
    ∃ ρ, ρ ∈ orders 6 ∧ ∀ M, M ∈ orders 6 → memB6 m M = H (rlab ρ M) := by
  obtain ⟨τ, hτ, hτm⟩ := h
  refine ⟨pinv 6 τ, pinv_mem_orders hτ, fun M hM => ?_⟩
  rw [hτm _ (rlab_mem_orders (pinv_mem_orders hτ) hM), rlab_rlab_pinv hτ]

theorem key6_of_isoM {m : Nat} {H : List Nat → Bool} (hH : DomE 6 H) (h : IsoM m H) : key6 (memB6 m) = key6 H := by
  obtain ⟨ρ, hρ, hρm⟩ := isoM_inv h
  rw [key6_congr hρm, key6_relabel hH hρ]

theorem isS_relabel_iff {H : List Nat → Bool} {π : List Nat} (hπ : π ∈ orders 6) :
    IsS (fun M => H (rlab π M)) ↔ IsS H := by
  unfold IsS
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (isoM_relabel_iff hπ).mp h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (isoM_relabel_iff hπ).mpr h⟩

theorem isS_congr {H H' : List Nat → Bool} (h : ∀ M, M ∈ orders 6 → H M = H' M) : IsS H ↔ IsS H' := by
  unfold IsS
  constructor
  · rintro ⟨i, hi, h'⟩; exact ⟨i, hi, (isoM_congr h).mp h'⟩
  · rintro ⟨i, hi, h'⟩; exact ⟨i, hi, (isoM_congr h).mpr h'⟩

/-- **The S type of a six-domain is unique.** -/
theorem sType_unique {H : List Nat → Bool} (hH : DomE 6 H) {i j : Nat} (hi : i < 9) (hj : j < 9)
    (h1 : IsoM (excRep6.getD i 0) H) (h2 : IsoM (excRep6.getD j 0) H) : i = j := by
  have e1 := key6_of_isoM hH h1
  have e2 := key6_of_isoM hH h2
  have hnd := sKeys_nodup
  have hl : ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0)))).length = 9 := by simp
  have hi' : i < ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0)))).length := by rw [hl]; exact hi
  have hj' : j < ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0)))).length := by rw [hl]; exact hj
  have heq : ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0))))[i] =
      ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0))))[j] := by
    simp only [List.getElem_map, List.getElem_range]
    rw [e1, e2]
  exact nodup_getElem_inj hnd hi' hj' heq

theorem sIdx_eq {H : List Nat → Bool} (hH : DomE 6 H) {i : Nat} (hi : i < 9) (h : IsoM (excRep6.getD i 0) H) :
    sIdx H = i := by
  have hS : IsS H := ⟨i, hi, h⟩
  obtain ⟨h1, h2⟩ := sIdx_spec hS
  exact sType_unique hH h1 hi h2 h

theorem sIdx_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    sIdx (fun M => H (rlab π M)) = sIdx H := by
  by_cases hS : IsS H
  · obtain ⟨h1, h2⟩ := sIdx_spec hS
    exact sIdx_eq (domE_relabel hH hπ) h1 ((isoM_relabel_iff hπ).mpr h2) |>.trans rfl
  · have hS' : ¬ IsS (fun M => H (rlab π M)) := fun h => hS ((isS_relabel_iff hπ).mp h)
    unfold sIdx
    rw [dif_neg hS, dif_neg hS']

theorem sIdx_congr {H H' : List Nat → Bool} (hH : DomE 6 H) (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    sIdx H = sIdx H' := by
  by_cases hS : IsS H
  · obtain ⟨h1, h2⟩ := sIdx_spec hS
    exact (sIdx_eq (domE_congr h hH) h1 ((isoM_congr h).mp h2)).symm
  · have hS' : ¬ IsS H' := fun h' => hS ((isS_congr h).mpr h')
    unfold sIdx
    rw [dif_neg hS, dif_neg hS']

theorem pD_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    pD (fun M => H (rlab π M)) = pD H := by
  unfold pD
  by_cases hS : IsS H
  · rw [if_pos hS, if_pos ((isS_relabel_iff hπ).mpr hS), sIdx_relabel hH hπ]
  · rw [if_neg hS, if_neg (fun h => hS ((isS_relabel_iff hπ).mp h)), rb_relabel hH hπ, rt_relabel hH hπ]

theorem pD_congr {H H' : List Nat → Bool} (hH : DomE 6 H) (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    pD H = pD H' := by
  unfold pD
  by_cases hS : IsS H
  · rw [if_pos hS, if_pos ((isS_congr h).mp hS), sIdx_congr hH h]
  · rw [if_neg hS, if_neg (fun h' => hS ((isS_congr h).mpr h')), rb_congr h, rt_congr h]

theorem thB_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    thB (fun M => H (rlab π M)) = thB H := by
  unfold thB; rw [sD_relabel hH hπ, pD_relabel hH hπ]
theorem thT_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    thT (fun M => H (rlab π M)) = thT H := by
  unfold thT; rw [sD_relabel hH hπ, pD_relabel hH hπ]
theorem qD_relabel {H : List Nat → Bool} (hH : DomE 6 H) {π : List Nat} (hπ : π ∈ orders 6) :
    qD (fun M => H (rlab π M)) = qD H := by
  unfold qD; rw [bD_relabel hH hπ, tD_relabel hH hπ, pD_relabel hH hπ]
theorem thB_congr {H H' : List Nat → Bool} (hH : DomE 6 H) (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    thB H = thB H' := by
  unfold thB; rw [sD_congr h, pD_congr hH h]
theorem thT_congr {H H' : List Nat → Bool} (hH : DomE 6 H) (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    thT H = thT H' := by
  unfold thT; rw [sD_congr h, pD_congr hH h]
theorem qD_congr {H H' : List Nat → Bool} (hH : DomE 6 H) (h : ∀ M, M ∈ orders 6 → H M = H' M) :
    qD H = qD H' := by
  unfold qD; rw [bD_congr h, tD_congr h, pD_congr hH h]

/-! ### Seven-domains -/

theorem sum7_relabel {F : (List Nat → Bool) → Int}
    (hF : ∀ H, DomE 6 H → ∀ σ, σ ∈ orders 6 → F (fun M => H (rlab σ M)) = F H)
    (hFc : ∀ H H', DomE 6 H → (∀ M, M ∈ orders 6 → H M = H' M) → F H = F H')
    {J : List Nat → Bool} (hJ : DomE 7 J) {π : List Nat} (hπ : π ∈ orders 7) :
    ((List.range 7).map (fun z => F (botP z (fun N => J (rlab π N))))).sum = ((List.range 7).map (fun z => F (botP z J))).sum ∧
    ((List.range 7).map (fun w => F (topP w (fun N => J (rlab π N))))).sum = ((List.range 7).map (fun w => F (topP w J))).sum := by
  constructor
  · have hb : ∀ z, z ∈ List.range 7 → F (botP z (fun N => J (rlab π N))) = F (botP (app π z) J) := by
      intro z hz
      have hz' := List.mem_range.mp hz
      have hd := domE_bot (app_lt hπ hz') hJ
      rw [hFc _ _ (domE_congr (fun L hL => (botP_relabel hπ hz' J hL).symm) (domE_relabel hd (slicePerm_mem hπ hz')))
        (fun L hL => botP_relabel hπ hz' J hL)]
      exact hF _ hd _ (slicePerm_mem hπ hz')
    rw [List.map_congr_left hb, sum_range_perm hπ (fun z => F (botP z J))]
  · have hb : ∀ w, w ∈ List.range 7 → F (topP w (fun N => J (rlab π N))) = F (topP (app π w) J) := by
      intro w hw
      have hw' := List.mem_range.mp hw
      have hd := domE_top (app_lt hπ hw') hJ
      rw [hFc _ _ (domE_congr (fun L hL => (topP_relabel hπ hw' J hL).symm) (domE_relabel hd (slicePerm_mem hπ hw')))
        (fun L hL => topP_relabel hπ hw' J hL)]
      exact hF _ hd _ (slicePerm_mem hπ hw')
    rw [List.map_congr_left hb, sum_range_perm hπ (fun w => F (topP w J))]

/-- **`Λ` is invariant under relabelling.** -/
theorem lamD_relabel {J : List Nat → Bool} (hJ : DomE 7 J) {π : List Nat} (hπ : π ∈ orders 7) :
    lamD (fun N => J (rlab π N)) = lamD J := by
  unfold lamD
  rw [(sum7_relabel (fun H hH σ hσ => thB_relabel hH hσ) (fun H H' hH h => thB_congr hH h) hJ hπ).1,
    (sum7_relabel (fun H hH σ hσ => thT_relabel hH hσ) (fun H H' hH h => thT_congr hH h) hJ hπ).2]

theorem lamD_congr {J J' : List Nat → Bool} (hJ : DomE 7 J) (h : ∀ N, N ∈ orders 7 → J N = J' N) :
    lamD J = lamD J' := by
  unfold lamD
  congr 1
  · congr 1
    apply List.map_congr_left
    intro z hz
    exact thB_congr (domE_bot (List.mem_range.mp hz) hJ)
      (fun L hL => h _ (append_up_mem_orders (List.mem_range.mp hz) hL))
  · congr 1
    apply List.map_congr_left
    intro w hw
    exact thT_congr (domE_top (List.mem_range.mp hw) hJ)
      (fun L hL => h _ (cons_up_mem_orders (List.mem_range.mp hw) hL))

end CDCert.K6
