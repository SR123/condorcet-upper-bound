/-
CDCert.K6.Leaf7Sem — **what the seven-level leaf test says**: for a seven-domain `J` whose seed
block is the seed, `leaf7 … (encS (maskOf base7 J)) = true` gives `2ηD |J| ≤ lamD J`, i.e.
`Λ(J) ≥ η|J|` for the potential `θ` of `CDCert.K6.Theta`.

* `sDs_eq`: the slice value `sDs` is `D s(H) + 12·2^60` (`sumV6_eq_sD`, the table fields);
* `sKey_eq`: the slice key is `key6 H`;
* `sP_eq`: if the slice is certified (`sOK`), `sP = 2D p(H) + 2^62`: a hinted slice has the
  hinted S type (`hint_iso`, `sIdx_eq`), an unhinted one whose key is not an S key is not S
  (`sKeys_mem`, `key6_of_isoM`);
* `leaf7_sem`: the leaf inequality is `Λ(J) ≥ η|J|`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Base7Sem
import CDCert.K6.R8
import CDCert.K6.Seven.HintIso

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Folds as sums -/

theorem sumBot_eq (T hintS psiT : KTree) (m : Nat) (ss : List Slc) :
    sumBot T hintS psiT m ss = (ss.map (fun s => sDs T m s.1 s.2.1 + sP T hintS psiT m s.1 s.2.1 s.2.2)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show Nat.add (Nat.add (sDs T m s.1 s.2.1) (sP T hintS psiT m s.1 s.2.1 s.2.2)) (sumBot T hintS psiT m ss) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem sumTop_eq (T hintS psiT : KTree) (m : Nat) (ss : List Slc) :
    sumTop T hintS psiT m ss = (ss.map (fun s => sDs T m s.1 s.2.1 + (off63 - sP T hintS psiT m s.1 s.2.1 s.2.2))).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show Nat.add (Nat.add (sDs T m s.1 s.2.1) (Nat.sub off63 (sP T hintS psiT m s.1 s.2.1 s.2.2))) (sumTop T hintS psiT m ss) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem cardJ_eq (T : KTree) (m : Nat) (ss : List Slc) : cardJ T m ss = (ss.map (fun s => sumOff (cCard T) m s.1)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show Nat.add (sumOff (cCard T) m s.1) (cardJ T m ss) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem allOK_eq (T hintS sKeyT : KTree) (m : Nat) (ss : List Slc) :
    allOK T hintS sKeyT m ss = ss.all (fun s => sOK T hintS sKeyT m s.1 s.2.1 s.2.2) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show Bool.and (sOK T hintS sKeyT m s.1 s.2.1 s.2.2) (allOK T hintS sKeyT m ss) = _
    rw [ih, List.all_cons]

theorem shiftRight_encS (x : Nat) : Nat.shiftRight (encS x) 64 = x := by
  unfold encS
  show ((x <<< 64) ||| ((x <<< 64) % hashP)) >>> 64 = x
  rw [shiftRight_lor_small _ _ (mod_hashP_lt _), Nat.shiftLeft_shiftRight]

theorem nsum_le_length {α : Type} (l : List α) (f : α → Nat) (h : ∀ x, x ∈ l → f x ≤ 1) :
    (l.map f).sum ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

/-! ### One slice -/

section Slice
variable {m : Nat} {s : Slc} {H : List Nat → Bool}

theorem cB_m5 (p : List Nat → Bool) : (cB table5 (m5 p) : Int) = vB5 (m5 p) + 2 ^ 60 := by
  rw [cB_eq]; unfold vB5
  by_cases h : m5 p = 0
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; omega

theorem cT_m5 (p : List Nat → Bool) : (cT table5 (m5 p) : Int) = vT5 (m5 p) + 2 ^ 60 := by
  rw [cT_eq]; unfold vT5
  by_cases h : m5 p = 0
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; omega

theorem nsum_cast {α : Type} (l : List α) (f : α → Nat) : (((l.map f).sum : Nat) : Int) = (l.map (fun a => (f a : Int))).sum :=
  (isum_cast l f).symm

theorem sDs_eq (hs : SliceOK m s H) (hH : DomE 6 H) :
    (sDs table5 m s.1 s.2.1 : Int) = sD H + 12 * 2 ^ 60 := by
  obtain ⟨h1, h2, _⟩ := hs
  have hc : ∀ x, x ∈ List.range 6 → cCard table5 (m5 (botP x H)) = card 5 (botP x H) :=
    fun x hx => cCard_m5 (domE_bot (List.mem_range.mp hx) hH)
  have h866 : ∀ x, x ∈ List.range 6 → c866 table5 (m5 (botP x H)) = isTy 866 (botP x H) := fun x _ => c866_m5 _
  have h41 : ∀ y, y ∈ List.range 6 → c41 table5 (m5 (topP y H)) = isTy 41 (topP y H) := fun y _ => c41_m5 _
  have hcard : ((List.range 6).map (fun x => card 5 (botP x H))).sum = card 6 H := (card_succ_bot 5 H).symm
  have e : sDs table5 m s.1 s.2.1 = ((List.range 6).map (fun x => cB table5 (m5 (botP x H)))).sum +
      ((List.range 6).map (fun y => cT table5 (m5 (topP y H)))).sum + cE * (card 6 H + 4 * (rb H + rt H)) := by
    unfold sDs
    rw [h1, h2, h1, h1, h2]
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [List.map_congr_left hc, List.map_congr_left h866, List.map_congr_left h41, hcard]
    rfl
  have eB : (((List.range 6).map (fun x => cB table5 (m5 (botP x H)))).sum : Int) =
      ((List.range 6).map (fun x => vB5 (m5 (botP x H)))).sum + 6 * 2 ^ 60 := by
    rw [nsum_cast, List.map_congr_left (fun x _ => cB_m5 (botP x H)), isum_map_add]
    congr 1
  have eT : (((List.range 6).map (fun y => cT table5 (m5 (topP y H)))).sum : Int) =
      ((List.range 6).map (fun y => vT5 (m5 (topP y H)))).sum + 6 * 2 ^ 60 := by
    rw [nsum_cast, List.map_congr_left (fun y _ => cT_m5 (topP y H)), isum_map_add]
    congr 1
  have hsv : sumV6 H = sD H - cE * (card 6 H + 4 * rb H + 4 * rt H) := by
    rcases hH with hH | hE
    · exact sumV6_eq_sD hH
    · obtain ⟨h1', h2', h3', h4', _⟩ := empty_facts hE
      have hs0 : sD H = 0 := by
        unfold thB at h4'
        rw [pD_notS (empty_notS hE), h2', h3'] at h4'
        simpa using h4'
      rw [sumV6_empty hE, h1', h2', h3', hs0]; simp
  unfold sumV6 at hsv
  rw [e, Int.natCast_add, Int.natCast_add, eB, eT, Int.natCast_mul, Int.natCast_add, Int.natCast_mul, Int.natCast_add]
  have hE : (cE : Int) = 58198140 := rfl
  rw [hE] at hsv ⊢
  omega

theorem sKey_eq (hs : SliceOK m s H) : sKey table5 m s.1 s.2.1 = key6 H := by
  obtain ⟨h1, h2, _⟩ := hs
  rw [key6_eq]
  unfold sKey
  rw [h1, h2, h1, h1, h2, h1, h2]

theorem sP_eq (hs : SliceOK m s H) (hH : DomE 6 H) (hok : sOK table5 hintS sKeyT m s.1 s.2.1 s.2.2 = true) :
    (sP table5 hintS psiT m s.1 s.2.1 s.2.2 : Int) = pD H + 2 ^ 62 ∧ sP table5 hintS psiT m s.1 s.2.1 s.2.2 ≤ 2 ^ 63 := by
  have hs' := hs
  obtain ⟨h1, h2, h3⟩ := hs
  unfold sP
  unfold sOK at hok
  rw [h3] at hok ⊢
  cases hh : hintS.find (maskOf (baseB 5) H) with
  | succ h =>
    show (psiT.find h : Int) = pD H + 2 ^ 62 ∧ psiT.find h ≤ 2 ^ 63
    obtain ⟨hlt, σ, hσ, hrow⟩ := hint_iso _ h hh
    have hiso : IsoM (excRep6.getD h 0) H := ⟨σ, hσ, iso_of_relabel_maskB hσ hrow⟩
    have hS : IsS H := ⟨h, hlt, hiso⟩
    refine ⟨?_, psiT_le h hlt⟩
    unfold pD
    rw [if_pos hS, sIdx_eq hH hlt hiso]
    unfold psiD
    omega
  | zero =>
    show ((Nat.sub (Nat.add (Nat.mul (Nat.mul 4 cE) (sumOff (c41 table5) m s.2.1)) off62)
        (Nat.mul (Nat.mul 4 cE) (sumOff (c866 table5) m s.1)) : Nat) : Int) = pD H + 2 ^ 62 ∧
      Nat.sub (Nat.add (Nat.mul (Nat.mul 4 cE) (sumOff (c41 table5) m s.2.1)) off62)
        (Nat.mul (Nat.mul 4 cE) (sumOff (c866 table5) m s.1)) ≤ 2 ^ 63
    rw [hh] at hok
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
    have hk : sKeyT.find (key6 H) = 0 := by
      rcases hok with hok | hok
      · exact absurd hok (by decide)
      · rw [← sKey_eq hs']; exact Nat.eq_of_beq_eq_true hok
    have hnS : ¬ IsS H := by
      rintro ⟨i, hi, hiso⟩
      have := sKeys_mem i hi
      rw [key6_of_isoM hH hiso, hk] at this
      exact this rfl
    rw [h1, h2]
    have hrb : ((List.range 6).map (fun x => c866 table5 (m5 (botP x H)))).sum = rb H := by
      unfold rb; exact congrArg List.sum (List.map_congr_left (fun x _ => c866_m5 _))
    have hrt : ((List.range 6).map (fun y => c41 table5 (m5 (topP y H)))).sum = rt H := by
      unfold rt; exact congrArg List.sum (List.map_congr_left (fun y _ => c41_m5 _))
    rw [hrb, hrt, pD_notS hnS]
    have hrb6 : rb H ≤ 6 := by
      unfold rb
      exact nsum_le_length (List.range 6) _ (fun x _ => isTy_le_one _ _)
    have hrt6 : rt H ≤ 6 := by
      unfold rt
      exact nsum_le_length (List.range 6) _ (fun y _ => isTy_le_one _ _)
    have hE : cE = 58198140 := rfl
    have h62 : off62 = 2 ^ 62 := rfl
    rw [h62]
    constructor
    · show ((Nat.sub (Nat.add (Nat.mul (Nat.mul 4 cE) (rt H)) (2 ^ 62)) (Nat.mul (Nat.mul 4 cE) (rb H)) : Nat) : Int) = _
      rw [hE]
      show (((4 * 58198140 * rt H + 2 ^ 62) - 4 * 58198140 * rb H : Nat) : Int) = 4 * ((58198140 : Nat) : Int) * ((rt H : Int) - rb H) + 2 ^ 62
      omega
    · show Nat.sub (Nat.add (Nat.mul (Nat.mul 4 cE) (rt H)) (2 ^ 62)) (Nat.mul (Nat.mul 4 cE) (rb H)) ≤ 2 ^ 63
      rw [hE]
      show (4 * 58198140 * rt H + 2 ^ 62) - 4 * 58198140 * rb H ≤ 2 ^ 63
      omega

end Slice

/-! ### The leaf -/

/-- The leaf test, unfolded (generic in the data, so no data is unfolded). -/
theorem leaf7_true {T hintS psiT sKeyT : KTree} {bots tops : List Slc} {oSeed seed e : Nat}
    (hs : blk720 (Nat.shiftRight e 64) oSeed = seed) (h : leaf7 T hintS psiT sKeyT bots tops oSeed seed e = true) :
    allOK T hintS sKeyT (Nat.shiftRight e 64) (bots ++ tops) = true ∧
      Nat.add (Nat.mul (Nat.mul 2 cE) (cardJ T (Nat.shiftRight e 64) bots)) off224 ≤
        Nat.add (sumBot T hintS psiT (Nat.shiftRight e 64) bots) (sumTop T hintS psiT (Nat.shiftRight e 64) tops) := by
  unfold leaf7 at h
  rw [hs, Nat.beq_refl] at h
  have h' : (allOK T hintS sKeyT (Nat.shiftRight e 64) (bots ++ tops) &&
      Nat.ble (Nat.add (Nat.mul (Nat.mul 2 cE) (cardJ T (Nat.shiftRight e 64) bots)) off224)
        (Nat.add (sumBot T hintS psiT (Nat.shiftRight e 64) bots) (sumTop T hintS psiT (Nat.shiftRight e 64) tops))) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨h'.1, Nat.le_of_ble_eq_true h'.2⟩

theorem isum_map_const {α : Type} (l : List α) (c : Int) : (l.map (fun _ => c)).sum = (l.length : Int) * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Int.natCast_add, Int.add_mul, Int.natCast_one,
      Int.one_mul, Int.add_comm]

/-- The slices of a leaf are certified. -/
def LeafOK (m : Nat) : Prop := ∀ x, x ∈ bots7 ++ tops7 → sOK table5 hintS sKeyT m x.1 x.2.1 x.2.2 = true

section Leaf
variable {J : List Nat → Bool} {m : Nat}

theorem leaf_bot (hJ : DomE 7 J) (hm : maskOf base7 J = m) (hok : LeafOK m) {z : Nat} (hz : z < 7) :
    (((sDs table5 m (descB z).1 (descB z).2.1 + sP table5 hintS psiT m (descB z).1 (descB z).2.1 (descB z).2.2 : Nat)) : Int) =
      thB (botP z J) + 2 ^ 64 := by
  have hs := sliceOK_descB J hz
  rw [hm] at hs
  have hd := domE_bot hz hJ
  have hok' := hok (descB z) (List.mem_append_left _ (by rw [bots7_map]; exact List.mem_map_of_mem (List.mem_range.mpr hz)))
  rw [Int.natCast_add, sDs_eq hs hd, (sP_eq hs hd hok').1]
  unfold thB
  omega

theorem leaf_top (hJ : DomE 7 J) (hm : maskOf base7 J = m) (hok : LeafOK m) {w : Nat} (hw : w < 7) :
    (((sDs table5 m (descT w).1 (descT w).2.1 + (off63 - sP table5 hintS psiT m (descT w).1 (descT w).2.1 (descT w).2.2) : Nat)) : Int) =
      thT (topP w J) + 2 ^ 64 := by
  have hs := sliceOK_descT J hw
  rw [hm] at hs
  have hd := domE_top hw hJ
  have hok' := hok (descT w) (List.mem_append_right _ (by rw [tops7_map]; exact List.mem_map_of_mem (List.mem_range.mpr hw)))
  obtain ⟨hp, hp63⟩ := sP_eq hs hd hok'
  have h63 : off63 = 2 ^ 63 := rfl
  rw [Int.natCast_add, sDs_eq hs hd, h63, Int.ofNat_sub hp63, hp]
  unfold thT
  omega

theorem leaf_card (hJ : DomE 7 J) (hm : maskOf base7 J = m) {z : Nat} (hz : z < 7) :
    sumOff (cCard table5) m (descB z).1 = card 6 (botP z J) := by
  have hs := sliceOK_descB J hz
  rw [hm] at hs
  rw [hs.1]
  have hd := domE_bot hz hJ
  rw [List.map_congr_left (fun x hx => cCard_m5 (domE_bot (List.mem_range.mp hx) hd))]
  exact (card_succ_bot 5 _).symm

theorem nsum_cast_congr {α : Type} (l : List α) (f : α → Nat) (g : α → Int) (c : Int)
    (h : ∀ a, a ∈ l → (f a : Int) = g a + c) : (((l.map f).sum : Nat) : Int) = (l.map g).sum + (l.length : Int) * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, Int.natCast_add, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.map_cons, List.sum_cons, List.length_cons,
      Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]
    omega

theorem leaf_sumB (hJ : DomE 7 J) (hm : maskOf base7 J = m) (hok : LeafOK m) :
    ((((List.range 7).map ((fun s => sDs table5 m s.1 s.2.1 + sP table5 hintS psiT m s.1 s.2.1 s.2.2) ∘ descB)).sum : Nat) : Int) =
      ((List.range 7).map (fun z => thB (botP z J))).sum + 7 * 2 ^ 64 := by
  have h := nsum_cast_congr (List.range 7) ((fun s => sDs table5 m s.1 s.2.1 + sP table5 hintS psiT m s.1 s.2.1 s.2.2) ∘ descB)
    (fun z => thB (botP z J)) (2 ^ 64) (fun z hz => leaf_bot hJ hm hok (List.mem_range.mp hz))
  rw [List.length_range] at h
  exact h

theorem leaf_sumT (hJ : DomE 7 J) (hm : maskOf base7 J = m) (hok : LeafOK m) :
    ((((List.range 7).map ((fun s => sDs table5 m s.1 s.2.1 + (off63 - sP table5 hintS psiT m s.1 s.2.1 s.2.2)) ∘ descT)).sum : Nat) : Int) =
      ((List.range 7).map (fun w => thT (topP w J))).sum + 7 * 2 ^ 64 := by
  have h := nsum_cast_congr (List.range 7) ((fun s => sDs table5 m s.1 s.2.1 + (off63 - sP table5 hintS psiT m s.1 s.2.1 s.2.2)) ∘ descT)
    (fun w => thT (topP w J)) (2 ^ 64) (fun w hw => leaf_top hJ hm hok (List.mem_range.mp hw))
  rw [List.length_range] at h
  exact h

theorem leaf_cardSum (hJ : DomE 7 J) (hm : maskOf base7 J = m) :
    ((List.range 7).map ((fun s => sumOff (cCard table5) m s.1) ∘ descB)).sum = card 7 J := by
  rw [card_succ_bot 6 J]
  exact congrArg List.sum (List.map_congr_left (fun z hz => leaf_card hJ hm (List.mem_range.mp hz)))

theorem leaf_arith (A B C n : Nat) (a b : Int) (hle : 2 * 58198140 * C + 224 * 2 ^ 60 ≤ A + B) (hC : C = n)
    (hA : (A : Int) = a + 7 * 2 ^ 64) (hB : (B : Int) = b + 7 * 2 ^ 64) : 2 * 58198140 * (n : Int) ≤ a + b := by
  omega

end Leaf

/-- **The seven-level leaf test, read off.** -/
theorem leaf7_sem {J : List Nat → Bool} (hJ : DomE 7 J) {oSeed seed : Nat}
    (hseed : blk720 (maskOf base7 J) oSeed = seed)
    (h : leaf7 table5 hintS psiT sKeyT bots7 tops7 oSeed seed (encS (maskOf base7 J)) = true) :
    2 * (cE : Int) * card 7 J ≤ lamD J := by
  obtain ⟨hok, hle'⟩ := leaf7_true (by rw [shiftRight_encS]; exact hseed) h
  rw [shiftRight_encS] at hok hle'
  rw [allOK_eq, List.all_eq_true] at hok
  generalize hm : maskOf base7 J = m at hok hle'
  rw [sumBot_eq, sumTop_eq, cardJ_eq, bots7_map, tops7_map, List.map_map, List.map_map, List.map_map] at hle'
  have h224 : off224 = 224 * 2 ^ 60 := rfl
  have hcE : cE = 58198140 := rfl
  rw [h224, hcE] at hle'
  simp only [Nat.add_eq, Nat.mul_eq] at hle'
  unfold lamD
  exact leaf_arith _ _ _ _ _ _ hle' (leaf_cardSum hJ hm) (leaf_sumB hJ hm hok) (leaf_sumT hJ hm hok)

end CDCert.K6
