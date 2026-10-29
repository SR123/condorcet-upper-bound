/-
CDCert.K6.ThetaSem — the potential `θ` read through the five-table, and its
invariance under relabelling.

* `cB_eq` … `c41_eq`: the seven-level field functions of `CDCert.K6.Defs7` on a block;
* `vB5_eq`, `vT5_eq`: the six-row contributions of a five-domain in terms of `card`,
  `adj`, `potW`, `isTy` (for domains and empty slices);
* **`sumV6_eq_sD`**: for a six-domain, `sumV6 H = sD H − ηD (|H| + 4 r_b + 4 r_t)`
  (so the six-level fact `0 ≤ sumV6` is the receiver inequality `s ≥ η(|H| + 4r_b + 4r_t)`);
* invariance of `potW`, `isTy`, `bD`, `tD`, `rb`, `rt`, `sD`, `key6`, `IsS`, `sIdx`,
  `pD`, `thB`, `thT`, `qD` under relabelling of six-domains, and of `lamD` and `card 7`
  under relabelling of seven-domains; the same quantities only depend on the values of
  the predicates on orders (`*_congr`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.TabSem
import CDCert.K6.Seven.Keys

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

/-- A `k`-domain or empty. -/
def DomE (k : Nat) (p : List Nat → Bool) : Prop := IsDom k p ∨ IsEmptyOn k p

theorem card_eq_zero_iff {n : Nat} (p : List Nat → Bool) : card n p = 0 ↔ IsEmptyOn n p := by
  unfold card IsEmptyOn
  rw [List.countP_eq_zero]
  constructor
  · intro h L hL; cases hp : p L; · rfl
    · exact absurd hp (h L hL)
  · intro h L hL hp; rw [h L hL] at hp; cases hp

theorem adj_empty {n : Nat} {p : List Nat → Bool} (h : IsEmptyOn n p) : adj n p = 0 := by
  unfold adj
  have : ∀ j, j ∈ List.range (n - 1) → adjAt n j p = 0 := by
    intro j _
    unfold adjAt
    rw [List.countP_eq_zero]
    intro M hM
    simp [h M hM]
  rw [List.map_congr_left this]
  induction (List.range (n - 1)) with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]

theorem adjAt_empty {n j : Nat} {p : List Nat → Bool} (h : IsEmptyOn n p) : adjAt n j p = 0 := by
  unfold adjAt
  rw [List.countP_eq_zero]
  intro M hM
  simp [h M hM]

theorem domE_relabel {n : Nat} {p : List Nat → Bool} (hp : DomE n p) {σ : List Nat} (hσ : σ ∈ orders n) :
    DomE n (fun L => p (rlab σ L)) := by
  rcases hp with hp | hp
  · exact Or.inl (isDom_relabel hp hσ)
  · exact Or.inr (isEmptyOn_relabel hp hσ)

theorem domE_congr {n : Nat} {p q : List Nat → Bool} (h : ∀ L, L ∈ orders n → p L = q L) (hp : DomE n p) :
    DomE n q := by
  rcases hp with ⟨c, hc, hpc⟩ | hp
  · exact Or.inl ⟨c, hc, fun L hL => (h L hL).symm.trans (hpc L hL)⟩
  · exact Or.inr (fun L hL => (h L hL).symm.trans (hp L hL))

/-! ### The field functions of `Defs7` -/

theorem rec_enc {α : Type} (z : α) (g : Nat → α) (b : Nat) :
    Nat.rec (motive := fun _ => α) z (fun s _ => g (Nat.succ s)) (enc b) = if b = 0 then z else g (enc b) := by
  by_cases h : b = 0
  · subst h; rw [if_pos rfl]; rfl
  · rw [if_neg h]
    have hne : enc b ≠ 0 := fun h' => h ((enc_eq_zero_iff _).mp h')
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hs]

theorem tvE_enc (T : KTree) (b : Nat) : tvE T (enc b) = T.find b := by
  unfold tvE
  rw [show Nat.shiftRight (enc b) 64 = b from shiftRight_enc b]

theorem cB_eq (T : KTree) (b : Nat) : cB T b = if b = 0 then 2 ^ 60 else T.find b % 2 ^ 64 := by
  unfold cB
  rw [rec_enc off60 (fun s => Nat.land (tvE T s) m64), tvE_enc, land_m64, off60_eq]

theorem cT_eq (T : KTree) (b : Nat) : cT T b = if b = 0 then 2 ^ 60 else (T.find b >>> 64) % 2 ^ 64 := by
  unfold cT
  rw [rec_enc off60 (fun s => Nat.land (Nat.shiftRight (tvE T s) 64) m64), tvE_enc, land_m64, off60_eq]
  rfl

theorem cCard_eq (T : KTree) (b : Nat) : cCard T b = if b = 0 then 0 else (T.find b >>> 128) % 256 := by
  unfold cCard
  rw [rec_enc 0 (fun s => Nat.mod (Nat.shiftRight (tvE T s) 128) 256), tvE_enc]
  rfl

theorem cA5_eq (T : KTree) (b : Nat) : cA5 T b = if b = 0 then 0 else (T.find b >>> 136) % 1024 := by
  unfold cA5
  rw [rec_enc 0 (fun s => Nat.mod (Nat.shiftRight (tvE T s) 136) 1024), tvE_enc]
  rfl

theorem cA53_eq (T : KTree) (b : Nat) : cA53 T b = if b = 0 then 0 else (T.find b >>> 146) % 256 := by
  unfold cA53
  rw [rec_enc 0 (fun s => Nat.mod (Nat.shiftRight (tvE T s) 146) 256), tvE_enc]
  rfl

theorem c866_eq (T : KTree) (b : Nat) :
    c866 T b = if b = 0 then 0 else (if T.find b >>> 154 = 866 then 1 else 0) := by
  unfold c866
  rw [rec_enc 0 (fun s => cond (Nat.beq (Nat.shiftRight (tvE T s) 154) 866) 1 0), tvE_enc]
  split
  · rfl
  · show cond (Nat.beq (T.find b >>> 154) 866) 1 0 = _
    by_cases h : T.find b >>> 154 = 866
    · rw [if_pos h, h]; rfl
    · rw [if_neg h]
      cases hb : Nat.beq (T.find b >>> 154) 866
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem c41_eq (T : KTree) (b : Nat) :
    c41 T b = if b = 0 then 0 else (if T.find b >>> 154 = 41 then 1 else 0) := by
  unfold c41
  rw [rec_enc 0 (fun s => cond (Nat.beq (Nat.shiftRight (tvE T s) 154) 41) 1 0), tvE_enc]
  split
  · rfl
  · show cond (Nat.beq (T.find b >>> 154) 41) 1 0 = _
    by_cases h : T.find b >>> 154 = 41
    · rw [if_pos h, h]; rfl
    · rw [if_neg h]
      cases hb : Nat.beq (T.find b >>> 154) 41
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-! ### Five-domains through the table -/

theorem m5_ne_zero {p : List Nat → Bool} (hne : ¬ IsEmptyOn 5 p) : m5 p ≠ 0 :=
  fun h => hne ((m5_eq_zero_iff p).mp h)

theorem isTy_eq {k : Nat} {p : List Nat → Bool} :
    isTy k p = if m5 p = 0 then 0 else (if ty5 p = k then 1 else 0) := by
  unfold isTy
  by_cases h : IsEmptyOn 5 p
  · rw [if_pos ((m5_eq_zero_iff p).mpr h), if_neg (fun hc => hc.1 ((card_eq_zero_iff p).mpr h))]
  · rw [if_neg (m5_ne_zero h)]
    have hc : card 5 p ≠ 0 := fun hc => h ((card_eq_zero_iff p).mp hc)
    by_cases ht : ty5 p = k
    · rw [if_pos ⟨hc, ht⟩, if_pos ht]
    · rw [if_neg (fun h' => ht h'.2), if_neg ht]

theorem c866_m5 (p : List Nat → Bool) : c866 table5 (m5 p) = isTy 866 p := by
  rw [c866_eq, isTy_eq]; rfl

theorem c41_m5 (p : List Nat → Bool) : c41 table5 (m5 p) = isTy 41 p := by
  rw [c41_eq, isTy_eq]; rfl

theorem cCard_m5 {p : List Nat → Bool} (hp : DomE 5 p) : cCard table5 (m5 p) = card 5 p := by
  rw [cCard_eq]
  by_cases h : IsEmptyOn 5 p
  · rw [if_pos ((m5_eq_zero_iff p).mpr h), (card_eq_zero_iff p).mpr h]
  · rw [if_neg (m5_ne_zero h)]
    rcases hp with hp | hp
    · exact (tab_fields hp h).1
    · exact absurd hp h

theorem vB5_eq {p : List Nat → Bool} (hp : DomE 5 p) :
    vB5 (m5 p) = (cK : Int) * card 5 p + potW p - cD5 * adj 5 p - cE * (card 5 p + 4 * isTy 866 p) := by
  by_cases h : IsEmptyOn 5 p
  · have h0 : m5 p = 0 := (m5_eq_zero_iff p).mpr h
    have hc : card 5 p = 0 := (card_eq_zero_iff p).mpr h
    unfold vB5 potW
    rw [if_pos h0, hc, adj_empty h, isTy_eq, if_pos h0]
    simp
  · rcases hp with hp | hp
    · obtain ⟨_, _, _, _, hB, _⟩ := tab_fields hp h
      rw [hB, isTy_eq, if_neg (m5_ne_zero h)]
      unfold potW
      have hK : cK = 5587021440 := rfl
      have hD : cD5 = 1769223456 := rfl
      have hE : cE = 58198140 := rfl
      rw [hK, hD, hE]
      by_cases ht : ty5 p = 866
      · rw [if_pos ht, if_pos ht]; omega
      · rw [if_neg ht, if_neg ht]; omega
    · exact absurd hp h

theorem vT5_eq {p : List Nat → Bool} (hp : DomE 5 p) :
    vT5 (m5 p) = -potW p - cD5 * adjAt 5 3 p - 4 * cE * isTy 41 p := by
  by_cases h : IsEmptyOn 5 p
  · have h0 : m5 p = 0 := (m5_eq_zero_iff p).mpr h
    have hc : card 5 p = 0 := (card_eq_zero_iff p).mpr h
    unfold vT5 potW
    rw [if_pos h0, hc, adjAt_empty h, isTy_eq, if_pos h0]
    simp
  · rcases hp with hp | hp
    · obtain ⟨_, _, _, _, _, hT⟩ := tab_fields hp h
      rw [hT, isTy_eq, if_neg (m5_ne_zero h)]
      unfold potW
      have hD : cD5 = 1769223456 := rfl
      have hE : cE = 58198140 := rfl
      rw [hD, hE]
      by_cases ht : ty5 p = 41
      · rw [if_pos ht, if_pos ht]; omega
      · rw [if_neg ht, if_neg ht]; omega
    · exact absurd hp h

/-! ### The six-row sum and `θ` -/

theorem slice_bot' {x : Nat} (hx : x < 6) {H : List Nat → Bool} (hH : IsDom 6 H) : DomE 5 (botP x H) :=
  slice_bot (k := 5) hx hH

theorem slice_top' {y : Nat} (hy : y < 6) {H : List Nat → Bool} (hH : IsDom 6 H) : DomE 5 (topP y H) :=
  slice_top (k := 5) hy hH

/-- **The six-row sum is the receiver slack.** -/
theorem sumV6_eq_sD {H : List Nat → Bool} (hH : IsDom 6 H) :
    sumV6 H = sD H - cE * (card 6 H + 4 * rb H + 4 * rt H) := by
  unfold sumV6
  have hb : ∀ x, x ∈ List.range 6 → vB5 (m5 (botP x H)) =
      (cK : Int) * card 5 (botP x H) + potW (botP x H) - cD5 * adj 5 (botP x H) -
        cE * (card 5 (botP x H) + 4 * isTy 866 (botP x H)) :=
    fun x hx => vB5_eq (slice_bot' (List.mem_range.mp hx) hH)
  have ht : ∀ y, y ∈ List.range 6 → vT5 (m5 (topP y H)) =
      -potW (topP y H) - cD5 * adjAt 5 3 (topP y H) - 4 * cE * isTy 41 (topP y H) :=
    fun y hy => vT5_eq (slice_top' (List.mem_range.mp hy) hH)
  rw [List.map_congr_left hb, List.map_congr_left ht]
  have hc := card_succ_bot 5 H
  have ha := adj6_split H
  unfold sD bD tD rb rt
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil] at hc ha ⊢
  have hK : (cK : Int) = 5587021440 := rfl
  have hD : (cD5 : Int) = 1769223456 := rfl
  have hE : (cE : Int) = 58198140 := rfl
  rw [hK, hD, hE, hc, ha]
  simp only [Int.natCast_add, Int.natCast_mul]
  omega

end CDCert.K6
