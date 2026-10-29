/-
CDCert.K6.Win — **windows as iterated slices**. Conditioning a `k`-domain on its first `j` orders'
alternatives is iterated top slicing, on its last ones iterated bottom slicing; summing a feature over
all slices of all orders gives sums over all windows and all exteriors.

* `tops G k j H`: the sum of `G` over the `j`-fold top slices of the `k`-domain `H` (all choices of
  the first `j` alternatives, in order); `bots G k j H`: the same for bottom slices;
* linearity and monotonicity on `DomE` domains (`tops_le`, `bots_le`, …): every iterated slice of a
  `DomE` domain is `DomE` (`domE_top`, `domE_bot`);
* `tops_card`, `bots_card`, `tops_adjAt`, `bots_adjAt`: cards and enabled swaps add up over slices;
* `bots_botP`, `tops_topP`: one more bottom (top) slice is one more summation level;
* **`bots_topP`**: a top slice taken after `j` bottom slices is a top slice taken before them (the top
  slice of a bottom slice is a bottom slice of a top slice, `topP_botP`, after reindexing the pairs).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.SevenFinal

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Iterated slice sums -/

/-- Sum of `G` over the `j`-fold top slices of a `k`-domain. -/
def tops (G : (List Nat → Bool) → Int) : Nat → Nat → (List Nat → Bool) → Int
  | _, 0, H => G H
  | 0, _ + 1, _ => 0
  | k + 1, j + 1, H => ((List.range (k + 1)).map (fun y => tops G k j (topP y H))).sum

/-- Sum of `G` over the `j`-fold bottom slices of a `k`-domain. -/
def bots (G : (List Nat → Bool) → Int) : Nat → Nat → (List Nat → Bool) → Int
  | _, 0, H => G H
  | 0, _ + 1, _ => 0
  | k + 1, j + 1, H => ((List.range (k + 1)).map (fun z => bots G k j (botP z H))).sum

theorem tops_zero (G : (List Nat → Bool) → Int) (k : Nat) (H : List Nat → Bool) : tops G k 0 H = G H := by
  cases k <;> rfl

theorem bots_zero (G : (List Nat → Bool) → Int) (k : Nat) (H : List Nat → Bool) : bots G k 0 H = G H := by
  cases k <;> rfl

theorem tops_succ (G : (List Nat → Bool) → Int) (k j : Nat) (H : List Nat → Bool) :
    tops G (k + 1) (j + 1) H = ((List.range (k + 1)).map (fun y => tops G k j (topP y H))).sum := rfl

theorem bots_succ (G : (List Nat → Bool) → Int) (k j : Nat) (H : List Nat → Bool) :
    bots G (k + 1) (j + 1) H = ((List.range (k + 1)).map (fun z => bots G k j (botP z H))).sum := rfl

/-! ### Sums of lists -/

theorem isum_le_isum {α : Type} (l : List α) (f g : α → Int) (h : ∀ a, a ∈ l → f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem isum_congr {α : Type} (l : List α) (f g : α → Int) (h : ∀ a, a ∈ l → f a = g a) :
    (l.map f).sum = (l.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

/-! ### Monotonicity and linearity -/

theorem tops_le {G G' : (List Nat → Bool) → Int} : ∀ (j k : Nat) (H : List Nat → Bool), j ≤ k → DomE k H →
    (∀ H', DomE (k - j) H' → G H' ≤ G' H') → tops G k j H ≤ tops G' k j H
  | 0, k, H, _, hH, h => by rw [tops_zero, tops_zero]; exact h H (by rw [Nat.sub_zero]; exact hH)
  | j + 1, 0, _, hj, _, _ => absurd hj (by omega)
  | j + 1, k + 1, H, hj, hH, h => by
    rw [tops_succ, tops_succ]
    apply isum_le_isum
    intro y hy
    exact tops_le j k (topP y H) (by omega) (domE_top (List.mem_range.mp hy) hH)
      (fun H' hH' => h H' (by rw [Nat.succ_sub_succ]; exact hH'))

theorem bots_le {G G' : (List Nat → Bool) → Int} : ∀ (j k : Nat) (H : List Nat → Bool), j ≤ k → DomE k H →
    (∀ H', DomE (k - j) H' → G H' ≤ G' H') → bots G k j H ≤ bots G' k j H
  | 0, k, H, _, hH, h => by rw [bots_zero, bots_zero]; exact h H (by rw [Nat.sub_zero]; exact hH)
  | j + 1, 0, _, hj, _, _ => absurd hj (by omega)
  | j + 1, k + 1, H, hj, hH, h => by
    rw [bots_succ, bots_succ]
    apply isum_le_isum
    intro z hz
    exact bots_le j k (botP z H) (by omega) (domE_bot (List.mem_range.mp hz) hH)
      (fun H' hH' => h H' (by rw [Nat.succ_sub_succ]; exact hH'))

theorem tops_congr {G G' : (List Nat → Bool) → Int} (j k : Nat) (H : List Nat → Bool) (hj : j ≤ k) (hH : DomE k H)
    (h : ∀ H', DomE (k - j) H' → G H' = G' H') : tops G k j H = tops G' k j H :=
  Int.le_antisymm (tops_le j k H hj hH (fun H' hH' => Int.le_of_eq (h H' hH')))
    (tops_le j k H hj hH (fun H' hH' => Int.le_of_eq (h H' hH').symm))

theorem bots_congr {G G' : (List Nat → Bool) → Int} (j k : Nat) (H : List Nat → Bool) (hj : j ≤ k) (hH : DomE k H)
    (h : ∀ H', DomE (k - j) H' → G H' = G' H') : bots G k j H = bots G' k j H :=
  Int.le_antisymm (bots_le j k H hj hH (fun H' hH' => Int.le_of_eq (h H' hH')))
    (bots_le j k H hj hH (fun H' hH' => Int.le_of_eq (h H' hH').symm))

theorem tops_add (G G' : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool),
    tops (fun H' => G H' + G' H') k j H = tops G k j H + tops G' k j H
  | 0, k, H => by rw [tops_zero, tops_zero, tops_zero]
  | j + 1, 0, _ => rfl
  | j + 1, k + 1, H => by
    rw [tops_succ, tops_succ, tops_succ, ← isum_map_add]
    exact isum_congr _ _ _ (fun y _ => tops_add G G' j k (topP y H))

theorem bots_add (G G' : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool),
    bots (fun H' => G H' + G' H') k j H = bots G k j H + bots G' k j H
  | 0, k, H => by rw [bots_zero, bots_zero, bots_zero]
  | j + 1, 0, _ => rfl
  | j + 1, k + 1, H => by
    rw [bots_succ, bots_succ, bots_succ, ← isum_map_add]
    exact isum_congr _ _ _ (fun z _ => bots_add G G' j k (botP z H))

theorem tops_mul (c : Int) (G : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool),
    tops (fun H' => c * G H') k j H = c * tops G k j H
  | 0, k, H => by rw [tops_zero, tops_zero]
  | j + 1, 0, _ => by show (0 : Int) = c * 0; rw [Int.mul_zero]
  | j + 1, k + 1, H => by
    rw [tops_succ, tops_succ, ← isum_map_mul]
    exact isum_congr _ _ _ (fun y _ => tops_mul c G j k (topP y H))

theorem bots_mul (c : Int) (G : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool),
    bots (fun H' => c * G H') k j H = c * bots G k j H
  | 0, k, H => by rw [bots_zero, bots_zero]
  | j + 1, 0, _ => by show (0 : Int) = c * 0; rw [Int.mul_zero]
  | j + 1, k + 1, H => by
    rw [bots_succ, bots_succ, ← isum_map_mul]
    exact isum_congr _ _ _ (fun z _ => bots_mul c G j k (botP z H))

/-! ### Cards and enabled swaps over slices -/

theorem tops_card : ∀ (j k : Nat) (H : List Nat → Bool), j ≤ k →
    tops (fun H' => (card (k - j) H' : Int)) k j H = card k H
  | 0, k, H, _ => by rw [tops_zero, Nat.sub_zero]
  | j + 1, 0, _, hj => absurd hj (by omega)
  | j + 1, k + 1, H, hj => by
    rw [tops_succ, card_succ_top, ← isum_cast]
    apply isum_congr
    intro y _
    have := tops_card j k (topP y H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

theorem bots_card : ∀ (j k : Nat) (H : List Nat → Bool), j ≤ k →
    bots (fun H' => (card (k - j) H' : Int)) k j H = card k H
  | 0, k, H, _ => by rw [bots_zero, Nat.sub_zero]
  | j + 1, 0, _, hj => absurd hj (by omega)
  | j + 1, k + 1, H, hj => by
    rw [bots_succ, card_succ_bot, ← isum_cast]
    apply isum_congr
    intro z _
    have := bots_card j k (botP z H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

theorem tops_adjAt (p : Nat) : ∀ (j k : Nat) (H : List Nat → Bool), p + 1 < k - j →
    tops (fun H' => (adjAt (k - j) p H' : Int)) k j H = adjAt k (p + j) H
  | 0, k, H, _ => by rw [tops_zero, Nat.sub_zero, Nat.add_zero]
  | j + 1, 0, _, hj => absurd hj (by omega)
  | j + 1, k + 1, H, hj => by
    rw [tops_succ, show p + (j + 1) = (p + j) + 1 by omega, adjAt_succ_top (by omega), ← isum_cast]
    apply isum_congr
    intro y _
    have := tops_adjAt p j k (topP y H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

theorem bots_adjAt (p : Nat) : ∀ (j k : Nat) (H : List Nat → Bool), p + 1 < k - j →
    bots (fun H' => (adjAt (k - j) p H' : Int)) k j H = adjAt k p H
  | 0, k, H, _ => by rw [bots_zero, Nat.sub_zero]
  | j + 1, 0, _, hj => absurd hj (by omega)
  | j + 1, k + 1, H, hj => by
    rw [bots_succ, adjAt_succ_bot (by omega), ← isum_cast]
    apply isum_congr
    intro z _
    have := bots_adjAt p j k (botP z H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

/-! ### One more slice -/

theorem bots_botP (G : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool), j < k →
    bots (fun J => ((List.range (k - j)).map (fun z => G (botP z J))).sum) k j H = bots G k (j + 1) H
  | 0, k + 1, H, _ => by
    rw [bots_zero, bots_succ, Nat.sub_zero]
    exact isum_congr _ _ _ (fun z _ => (bots_zero G k (botP z H)).symm)
  | 0, 0, _, h => absurd h (by omega)
  | j + 1, 0, _, h => absurd h (by omega)
  | j + 1, k + 1, H, h => by
    rw [bots_succ, bots_succ]
    apply isum_congr
    intro z _
    have := bots_botP G j k (botP z H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

theorem tops_topP (G : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool), j < k →
    tops (fun J => ((List.range (k - j)).map (fun y => G (topP y J))).sum) k j H = tops G k (j + 1) H
  | 0, k + 1, H, _ => by
    rw [tops_zero, tops_succ, Nat.sub_zero]
    exact isum_congr _ _ _ (fun y _ => (tops_zero G k (topP y H)).symm)
  | 0, 0, _, h => absurd h (by omega)
  | j + 1, 0, _, h => absurd h (by omega)
  | j + 1, k + 1, H, h => by
    rw [tops_succ, tops_succ]
    apply isum_congr
    intro y _
    have := tops_topP G j k (topP y H) (by omega)
    rw [Nat.succ_sub_succ]
    exact this

/-! ### Reindexing pairs of labels -/

theorem nodup_flatMap_of {α β : Type} : ∀ {l : List α} {f : α → List β}, l.Nodup → (∀ a, a ∈ l → (f a).Nodup) →
    (∀ a, a ∈ l → ∀ b, b ∈ l → a ≠ b → ∀ x, x ∈ f a → x ∉ f b) → (l.flatMap f).Nodup
  | [], _, _, _, _ => List.nodup_nil
  | a :: l, f, hl, hf, hd => by
    rw [List.flatMap_cons, List.nodup_append]
    have hal := List.nodup_cons.mp hl
    refine ⟨hf a List.mem_cons_self,
      nodup_flatMap_of hal.2 (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc hbc => hd b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hbc), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    have hab : a ≠ b := fun h => hal.1 (h ▸ hb)
    exact hd a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hab x hx hxb

theorem nodup_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, hl => by
    rw [List.map_cons, List.nodup_cons]
    have hal := List.nodup_cons.mp hl
    refine ⟨fun h => ?_, nodup_map_of_inj hf hal.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp h
    exact hal.1 (hf b a hfb ▸ hb)

/-- Pairs `(z, y)`, `z ≤ k`, `y < k`. -/
def prsK (k : Nat) : List (Nat × Nat) := (List.range (k + 1)).flatMap (fun z => (List.range k).map (fun y => (z, y)))

theorem mem_prsK {k : Nat} {p : Nat × Nat} : p ∈ prsK k ↔ p.1 < k + 1 ∧ p.2 < k := by
  obtain ⟨z, y⟩ := p
  unfold prsK
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨z', hz, y', hy, rfl, rfl⟩
    exact ⟨hz, hy⟩
  · rintro ⟨hz, hy⟩
    exact ⟨z, hz, y, hy, rfl, rfl⟩

theorem nodup_prsK (k : Nat) : (prsK k).Nodup := by
  unfold prsK
  apply nodup_flatMap_of List.nodup_range
  · intro z _
    exact nodup_map_of_inj (fun a b h => (Prod.mk.inj h).2) List.nodup_range
  · intro a _ b _ hab x hxa hxb
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hxa
    obtain ⟨y', _, hy'⟩ := List.mem_map.mp hxb
    exact hab (Prod.mk.inj hy').1.symm

/-- The relabelling of pairs behind `topP_botP`. -/
def swapPr (p : Nat × Nat) : Nat × Nat := (up p.1 p.2, down (up p.1 p.2) p.1)

theorem swapPr_swapPr (p : Nat × Nat) : swapPr (swapPr p) = p := by
  obtain ⟨z, y⟩ := p
  unfold swapPr
  simp only
  have hne : z ≠ up z y := fun h => up_ne z y h.symm
  rw [up_down hne, down_up]

theorem swapPr_mem {k : Nat} {p : Nat × Nat} (hp : p ∈ prsK k) : swapPr p ∈ prsK k := by
  obtain ⟨z, y⟩ := p
  rw [mem_prsK] at hp ⊢
  obtain ⟨hz, hy⟩ := hp
  exact ⟨up_lt hz hy, down_lt hz (fun h => up_ne z y h.symm) (up_lt hz hy)⟩

theorem perm_swapPr (k : Nat) : ((prsK k).map swapPr).Perm (prsK k) := by
  apply perm_of_nodup_of_mem_iff' (nodup_map_of_inj (fun a b h => by
    rw [← swapPr_swapPr a, h, swapPr_swapPr]) (nodup_prsK k)) (nodup_prsK k)
  intro q
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact swapPr_mem hp
  · intro h
    exact List.mem_map.mpr ⟨swapPr q, swapPr_mem h, swapPr_swapPr q⟩

/-- **Reindexing**: `(z, y) ↦ (up z y, down (up z y) z)` permutes the pairs. -/
theorem isum_swap (k : Nat) (F : Nat → Nat → Int) :
    ((List.range (k + 1)).map (fun z => ((List.range k).map (fun y => F (up z y) (down (up z y) z))).sum)).sum =
      ((List.range (k + 1)).map (fun w => ((List.range k).map (fun x => F w x)).sum)).sum := by
  have e1 : ((List.range (k + 1)).map (fun z => ((List.range k).map (fun y => F (up z y) (down (up z y) z))).sum)).sum =
      (((prsK k).map swapPr).map (fun q => F q.1 q.2)).sum := by
    unfold prsK
    rw [List.map_map, isum_flatMap]
    apply isum_congr
    intro z _
    rw [List.map_map]
    rfl
  have e2 : ((List.range (k + 1)).map (fun w => ((List.range k).map (fun x => F w x)).sum)).sum =
      ((prsK k).map (fun q => F q.1 q.2)).sum := by
    unfold prsK
    rw [isum_flatMap]
    apply isum_congr
    intro z _
    rw [List.map_map]
    rfl
  rw [e1, e2]
  exact perm_sum_int ((perm_swapPr k).map _)

/-- **A top slice after `j` bottom slices is a top slice before them.** -/
theorem bots_topP (G : (List Nat → Bool) → Int) : ∀ (j k : Nat) (H : List Nat → Bool), j < k →
    bots (fun J => ((List.range (k - j)).map (fun w => G (topP w J))).sum) k j H =
      ((List.range k).map (fun y => bots G (k - 1) j (topP y H))).sum
  | 0, k + 1, H, _ => by
    rw [bots_zero, Nat.sub_zero, show k + 1 - 1 = k from rfl]
    exact isum_congr _ _ _ (fun y _ => (bots_zero G k (topP y H)).symm)
  | 0, 0, _, h => absurd h (by omega)
  | j + 1, 0, _, h => absurd h (by omega)
  | j + 1, 0 + 1, _, h => absurd h (by omega)
  | j + 1, k + 1 + 1, H, h => by
    rw [bots_succ]
    have hF : ∀ z, z ∈ List.range (k + 1 + 1) →
        bots (fun J => ((List.range (k + 1 + 1 - (j + 1))).map (fun w => G (topP w J))).sum) (k + 1) j (botP z H) =
          ((List.range (k + 1)).map (fun y => bots G k j (botP (down (up z y) z) (topP (up z y) H)))).sum := by
      intro z _
      have := bots_topP G j (k + 1) (botP z H) (by omega)
      rw [show k + 1 + 1 - (j + 1) = k + 1 - j by omega, this, show k + 1 - 1 = k from rfl]
      apply isum_congr
      intro y _
      rw [topP_botP]
    rw [isum_congr _ _ _ hF, isum_swap (k + 1) (fun w x => bots G k j (botP x (topP w H))),
      show k + 1 + 1 - 1 = k + 1 from rfl]
    apply isum_congr
    intro w _
    rw [bots_succ]

/-! ### `q` is bounded by a multiple of the size -/

theorem potT_lt : ∀ k, k < 1160 → potT.find k < 2 ^ 41 := by decide +kernel

theorem potW_bound {p : List Nat → Bool} (hp : DomE 5 p) :
    -(2 ^ 40 * (card 5 p : Int)) ≤ potW p ∧ potW p ≤ 2 ^ 40 * (card 5 p : Int) := by
  unfold potW
  by_cases h0 : card 5 p = 0
  · rw [h0]; simp
  · have hne : ¬ IsEmptyOn 5 p := fun hE => h0 ((card_eq_zero_iff p).mpr hE)
    have hd : IsDom 5 p := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp hne
    have hty := (tab_fields hd hne).2.2.2.1
    have hlt := potT_lt _ hty
    unfold pot5
    have hc : (0 : Int) ≤ card 5 p := Int.natCast_nonneg _
    have h1 : (0 : Int) ≤ (potT.find (ty5 p) : Int) := Int.natCast_nonneg _
    have h2 : ((potT.find (ty5 p) : Nat) : Int) < 2 ^ 41 := by exact_mod_cast hlt
    constructor
    · have : (card 5 p : Int) * ((potT.find (ty5 p) : Int) - 2 ^ 40) + 2 ^ 40 * card 5 p =
          (card 5 p : Int) * (potT.find (ty5 p) : Int) := by rw [Int.mul_sub]; omega
      have h3 : (0 : Int) ≤ (card 5 p : Int) * (potT.find (ty5 p) : Int) := Int.mul_nonneg hc h1
      omega
    · have : 2 ^ 40 * (card 5 p : Int) - (card 5 p : Int) * ((potT.find (ty5 p) : Int) - 2 ^ 40) =
          (card 5 p : Int) * (2 ^ 41 - (potT.find (ty5 p) : Int)) := by
        rw [Int.mul_sub, Int.mul_sub]; omega
      have h3 : (0 : Int) ≤ (card 5 p : Int) * (2 ^ 41 - (potT.find (ty5 p) : Int)) :=
        Int.mul_nonneg hc (by omega)
      omega

theorem isum_abs_le {α : Type} (l : List α) (f g : α → Int) (h : ∀ a, a ∈ l → -g a ≤ f a ∧ f a ≤ g a) :
    -(l.map g).sum ≤ (l.map f).sum ∧ (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem bD_bound {H : List Nat → Bool} (hH : DomE 6 H) :
    -(2 ^ 40 * (card 6 H : Int)) ≤ bD H ∧ bD H ≤ 2 ^ 40 * (card 6 H : Int) := by
  unfold bD
  have hc : (card 6 H : Int) = ((List.range 6).map (fun x => (card 5 (botP x H) : Int))).sum := by
    rw [isum_cast, ← card_succ_bot]
  have := isum_abs_le (List.range 6) (fun x => potW (botP x H)) (fun x => 2 ^ 40 * (card 5 (botP x H) : Int))
    (fun x hx => potW_bound (domE_bot (List.mem_range.mp hx) hH))
  rw [isum_map_mul, ← hc] at this
  exact this

theorem tD_bound {H : List Nat → Bool} (hH : DomE 6 H) :
    -(2 ^ 40 * (card 6 H : Int)) ≤ tD H ∧ tD H ≤ 2 ^ 40 * (card 6 H : Int) := by
  unfold tD
  have hc : (card 6 H : Int) = ((List.range 6).map (fun y => (card 5 (topP y H) : Int))).sum := by
    rw [isum_cast, ← card_succ_top]
  have := isum_abs_le (List.range 6) (fun y => potW (topP y H)) (fun y => 2 ^ 40 * (card 5 (topP y H) : Int))
    (fun y hy => potW_bound (domE_top (List.mem_range.mp hy) hH))
  rw [isum_map_mul, ← hc] at this
  exact this

theorem pD_bound (H : List Nat → Bool) :
    -(2 ^ 62 * (card 6 H : Int)) ≤ pD H ∧ pD H ≤ 2 ^ 62 * (card 6 H : Int) := by
  by_cases h0 : card 6 H = 0
  · have hE : IsEmptyOn 6 H := (card_eq_zero_iff H).mp h0
    obtain ⟨_, h2, h3, _, _⟩ := empty_facts hE
    rw [pD_notS (empty_notS hE), h2, h3, h0]
    simp
  · have hc : (1 : Int) ≤ card 6 H := by have : 1 ≤ card 6 H := Nat.pos_of_ne_zero h0; exact_mod_cast this
    have hb : (2 ^ 62 : Int) ≤ 2 ^ 62 * (card 6 H : Int) := by
      have := Int.mul_le_mul_of_nonneg_left hc (by decide : (0 : Int) ≤ 2 ^ 62)
      rw [Int.mul_one] at this
      exact this
    have hp : -(2 ^ 62 : Int) ≤ pD H ∧ pD H ≤ 2 ^ 62 := by
      unfold pD
      by_cases hS : IsS H
      · rw [@if_pos _ (Classical.propDecidable _) hS]
        have hi := (sIdx_spec hS).1
        have := psiT_le _ hi
        unfold psiD
        have h1 : (0 : Int) ≤ (psiT.find (sIdx H) : Int) := Int.natCast_nonneg _
        have h2 : ((psiT.find (sIdx H) : Nat) : Int) ≤ 2 ^ 63 := by exact_mod_cast this
        constructor <;> omega
      · rw [@if_neg _ (Classical.propDecidable _) hS]
        have hrb : rb H ≤ 6 := by
          unfold rb; exact nsum_le_length (List.range 6) _ (fun x _ => isTy_le_one _ _)
        have hrt : rt H ≤ 6 := by
          unfold rt; exact nsum_le_length (List.range 6) _ (fun y _ => isTy_le_one _ _)
        have hE : (cE : Int) = 58198140 := rfl
        rw [hE]
        have h1 : ((rb H : Nat) : Int) ≤ 6 := by exact_mod_cast hrb
        have h2 : ((rt H : Nat) : Int) ≤ 6 := by exact_mod_cast hrt
        have h3 : (0 : Int) ≤ rb H := Int.natCast_nonneg _
        have h4 : (0 : Int) ≤ rt H := Int.natCast_nonneg _
        constructor <;> omega
    constructor <;> omega

/-- `|2D q(H)| ≤ 2^63 |H|`. -/
theorem qD_bound {H : List Nat → Bool} (hH : DomE 6 H) :
    -(2 ^ 63 * (card 6 H : Int)) ≤ qD H ∧ qD H ≤ 2 ^ 63 * (card 6 H : Int) := by
  unfold qD
  have h1 := bD_bound hH
  have h2 := tD_bound hH
  have h3 := pD_bound H
  have hc : (0 : Int) ≤ card 6 H := Int.natCast_nonneg _
  constructor <;> omega

/-! ### Windows -/

/-- Sum of `G` over all conditional domains of window `i` (positions `i … i+w-1`) of an `n`-domain:
`i` top slices, then `n - w - i` bottom slices. -/
def winS (G : (List Nat → Bool) → Int) (n w i : Nat) (K : List Nat → Bool) : Int :=
  tops (fun H => bots G (n - i) (n - w - i) H) n i K

theorem winS_le {G G' : (List Nat → Bool) → Int} {n w i : Nat} {K : List Nat → Bool} (hi : i + w ≤ n)
    (hK : DomE n K) (h : ∀ J, DomE w J → G J ≤ G' J) : winS G n w i K ≤ winS G' n w i K := by
  unfold winS
  apply tops_le i n K (by omega) hK
  intro H hH
  apply bots_le (n - w - i) (n - i) H (by omega) hH
  intro J hJ
  rw [show n - i - (n - w - i) = w by omega] at hJ
  exact h J hJ

theorem winS_add (G G' : (List Nat → Bool) → Int) (n w i : Nat) (K : List Nat → Bool) :
    winS (fun J => G J + G' J) n w i K = winS G n w i K + winS G' n w i K := by
  unfold winS
  rw [← tops_add]
  congr 1
  funext H
  exact bots_add G G' _ _ H

theorem winS_mul (c : Int) (G : (List Nat → Bool) → Int) (n w i : Nat) (K : List Nat → Bool) :
    winS (fun J => c * G J) n w i K = c * winS G n w i K := by
  unfold winS
  rw [← tops_mul]
  congr 1
  funext H
  exact bots_mul c G _ _ H

theorem winS_sub (G G' : (List Nat → Bool) → Int) (n w i : Nat) (K : List Nat → Bool) :
    winS (fun J => G J - G' J) n w i K = winS G n w i K - winS G' n w i K := by
  have e : (fun J => G J - G' J) = (fun J => G J + (-1) * G' J) := by
    funext J; rw [Int.sub_eq_add_neg, Int.neg_one_mul]
  rw [e, winS_add, winS_mul]
  omega

theorem winS_card {n w i : Nat} (K : List Nat → Bool) (hi : i + w ≤ n) :
    winS (fun J => (card w J : Int)) n w i K = card n K := by
  unfold winS
  have e : (fun H => bots (fun J => (card w J : Int)) (n - i) (n - w - i) H) =
      (fun H => bots (fun J => (card ((n - i) - (n - w - i)) J : Int)) (n - i) (n - w - i) H) := by
    rw [show n - i - (n - w - i) = w by omega]
  rw [e]
  have e2 : (fun H => bots (fun J => (card ((n - i) - (n - w - i)) J : Int)) (n - i) (n - w - i) H) =
      (fun H => (card (n - i) H : Int)) := by
    funext H
    exact bots_card _ _ H (by omega)
  rw [e2]
  exact tops_card i n K (by omega)

theorem winS_adjAt {n w i p : Nat} (K : List Nat → Bool) (hi : i + w ≤ n) (hp : p + 1 < w) :
    winS (fun J => (adjAt w p J : Int)) n w i K = adjAt n (p + i) K := by
  unfold winS
  have e : (fun H => bots (fun J => (adjAt w p J : Int)) (n - i) (n - w - i) H) =
      (fun H => bots (fun J => (adjAt ((n - i) - (n - w - i)) p J : Int)) (n - i) (n - w - i) H) := by
    rw [show n - i - (n - w - i) = w by omega]
  rw [e]
  have e2 : (fun H => bots (fun J => (adjAt ((n - i) - (n - w - i)) p J : Int)) (n - i) (n - w - i) H) =
      (fun H => (adjAt (n - i) p H : Int)) := by
    funext H
    exact bots_adjAt p _ _ H (by omega)
  rw [e2]
  exact tops_adjAt p i n K (by omega)

theorem winS_bot {n i : Nat} (K : List Nat → Bool) (hi : i + 7 ≤ n) :
    winS (fun J => ((List.range 7).map (fun z => qD (botP z J))).sum) n 7 i K = winS qD n 6 i K := by
  unfold winS
  congr 1
  funext H
  have := bots_botP qD (n - 7 - i) (n - i) H (by omega)
  rw [show n - i - (n - 7 - i) = 7 by omega, show n - 7 - i + 1 = n - 6 - i by omega] at this
  exact this

theorem winS_top {n i : Nat} (K : List Nat → Bool) (hi : i + 7 ≤ n) :
    winS (fun J => ((List.range 7).map (fun w => qD (topP w J))).sum) n 7 i K = winS qD n 6 (i + 1) K := by
  unfold winS
  have e : (fun H => bots (fun J => ((List.range 7).map (fun w => qD (topP w J))).sum) (n - i) (n - 7 - i) H) =
      (fun H => ((List.range (n - i)).map (fun y => bots qD (n - (i + 1)) (n - 6 - (i + 1)) (topP y H))).sum) := by
    funext H
    have := bots_topP qD (n - 7 - i) (n - i) H (by omega)
    rw [show n - i - (n - 7 - i) = 7 by omega, show n - i - 1 = n - (i + 1) by omega,
      show n - 7 - i = n - 6 - (i + 1) by omega] at this
    rw [show n - 7 - i = n - 6 - (i + 1) by omega]
    exact this
  rw [e]
  have := tops_topP (fun H' => bots qD (n - (i + 1)) (n - 6 - (i + 1)) H') i n K (by omega)
  exact this

/-! ### The window inequality -/

theorem cost10_int (J : List Nat → Bool) : (cost10 J : Int) =
    (adjAt 7 0 J : Int) + 2 * (adjAt 7 1 J : Int) + 2 * (adjAt 7 2 J : Int) + 2 * (adjAt 7 3 J : Int) +
      2 * (adjAt 7 4 J : Int) + (adjAt 7 5 J : Int) := by
  unfold cost10
  push_cast
  omega

theorem winS_cost10 {n i : Nat} (K : List Nat → Bool) (hi : i + 7 ≤ n) :
    winS (fun J => (cost10 J : Int)) n 7 i K =
      (adjAt n (0 + i) K : Int) + 2 * (adjAt n (1 + i) K : Int) + 2 * (adjAt n (2 + i) K : Int) +
        2 * (adjAt n (3 + i) K : Int) + 2 * (adjAt n (4 + i) K : Int) + (adjAt n (5 + i) K : Int) := by
  have e : (fun J => (cost10 J : Int)) = (fun J => (adjAt 7 0 J : Int) + 2 * (adjAt 7 1 J : Int) +
      2 * (adjAt 7 2 J : Int) + 2 * (adjAt 7 3 J : Int) + 2 * (adjAt 7 4 J : Int) + (adjAt 7 5 J : Int)) := by
    funext J; exact cost10_int J
  rw [e]
  simp only [winS_add, winS_mul]
  rw [winS_adjAt K hi (by decide : 0 + 1 < 7), winS_adjAt K hi (by decide : 1 + 1 < 7),
    winS_adjAt K hi (by decide : 2 + 1 < 7), winS_adjAt K hi (by decide : 3 + 1 < 7),
    winS_adjAt K hi (by decide : 4 + 1 < 7), winS_adjAt K hi (by decide : 5 + 1 < 7)]

/-- **The finite lemma on one window**, summed over its exteriors. -/
theorem window_ineq {n i : Nat} {K : List Nat → Bool} (hK : DomE n K) (hi : i + 7 ≤ n) :
    (cD5 : Int) * winS (fun J => (cost10 J : Int)) n 7 i K ≤
      11057646600 * card n K + winS qD n 6 i K - winS qD n 6 (i + 1) K := by
  have h := winS_le (G := fun J => (cD5 : Int) * (cost10 J : Int))
    (G' := fun J => 11057646600 * (card 7 J : Int) + ((List.range 7).map (fun z => qD (botP z J))).sum -
      ((List.range 7).map (fun w => qD (topP w J))).sum) hi hK (fun J hJ => finite_lemma hJ)
  rw [winS_mul, winS_sub, winS_add, winS_mul, winS_card K hi, winS_bot K hi, winS_top K hi] at h
  exact h

theorem winS_qD_bound {n i : Nat} {K : List Nat → Bool} (hK : DomE n K) (hi : i + 6 ≤ n) :
    -(2 ^ 63 * (card n K : Int)) ≤ winS qD n 6 i K ∧ winS qD n 6 i K ≤ 2 ^ 63 * (card n K : Int) := by
  have h1 := winS_le (G := qD) (G' := fun J => 2 ^ 63 * (card 6 J : Int)) hi hK (fun J hJ => (qD_bound hJ).2)
  have h2 := winS_le (G := fun J => -1 * (2 ^ 63 * (card 6 J : Int))) (G' := qD) hi hK
    (fun J hJ => by show -1 * (2 ^ 63 * (card 6 J : Int)) ≤ qD J; have := (qD_bound hJ).1; omega)
  rw [winS_mul, winS_card K hi] at h1
  rw [winS_mul, winS_mul, winS_card K hi] at h2
  constructor <;> omega

theorem isum_telescope (f : Nat → Int) : ∀ m, ((List.range m).map (fun i => f i - f (i + 1))).sum = f 0 - f m
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, isum_append, isum_telescope f m]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem isum_range_split (f : Nat → Int) (j m r : Nat) :
    ((List.range (j + m + r)).map f).sum = ((List.range j).map f).sum +
      ((List.range m).map (fun q => f (j + q))).sum + ((List.range r).map (fun s => f (j + m + s))).sum := by
  have h1 : List.range (j + m + r) =
      List.range j ++ (List.range m).map (fun q => j + q) ++ (List.range r).map (fun s => j + m + s) := by
    rw [List.range_add, List.range_add]
  rw [h1, List.map_append, List.map_append, isum_append, isum_append, List.map_map, List.map_map]
  all_goals rfl

theorem adjAt_le_card (k j : Nat) (H : List Nat → Bool) : adjAt k j H ≤ card k H :=
  List.countP_mono_left (fun _ _ h => (Bool.and_eq_true _ _).mp h |>.1)

theorem isum_le_const {α : Type} (l : List α) (f : α → Int) (c : Int) (h : ∀ a, a ∈ l → f a ≤ c) :
    (l.map f).sum ≤ (l.length : Int) * c := by
  rw [← isum_map_const]
  exact isum_le_isum l f (fun _ => c) h

/-- Each shifted run of `n - 6` positions misses at most five positions. -/
theorem shifted_adj {n j : Nat} (K : List Nat → Bool) (hn : 7 ≤ n) (hj : j ≤ 5) :
    (adj n K : Int) - 5 * card n K ≤ ((List.range (n - 6)).map (fun i => (adjAt n (j + i) K : Int))).sum := by
  have hs := isum_range_split (fun p => (adjAt n p K : Int)) j (n - 6) (5 - j)
  rw [show j + (n - 6) + (5 - j) = n - 1 by omega] at hs
  have ha : (adj n K : Int) = ((List.range (n - 1)).map (fun p => (adjAt n p K : Int))).sum := by
    rw [adj_eq, isum_cast]
  have hb : ∀ p, (adjAt n p K : Int) ≤ card n K := fun p => by exact_mod_cast adjAt_le_card n p K
  have h1 := isum_le_const (List.range j) (fun p => (adjAt n p K : Int)) (card n K) (fun p _ => hb p)
  have h2 := isum_le_const (List.range (5 - j)) (fun s => (adjAt n (j + (n - 6) + s) K : Int)) (card n K)
    (fun s _ => hb _)
  rw [List.length_range] at h1 h2
  have hc : (0 : Int) ≤ card n K := Int.natCast_nonneg _
  have e1 : ((j : Nat) : Int) * (card n K : Int) + (((5 - j : Nat) : Int)) * (card n K : Int) = 5 * (card n K : Int) := by
    rw [← Int.add_mul]
    congr 1
    omega
  omega

/-- **The window inequality**: for every `n`-domain, `n ≥ 7`,
`8 D A(K) ≤ 5 D n |K| + (10 D + 2^66) |K|`. -/
theorem window_bound {n : Nat} {K : List Nat → Bool} (hK : DomE n K) (hn : 7 ≤ n) :
    8 * 8846117280 * (adj n K : Int) ≤ 5 * 8846117280 * ((n : Int) * card n K) + (10 * 8846117280 + 2 ^ 66) * card n K := by
  -- sum the window inequalities
  have hsum : ((List.range (n - 6)).map (fun i => (cD5 : Int) * winS (fun J => (cost10 J : Int)) n 7 i K)).sum ≤
      ((List.range (n - 6)).map (fun i => 11057646600 * (card n K : Int) +
        (winS qD n 6 i K - winS qD n 6 (i + 1) K))).sum := by
    apply isum_le_isum
    intro i hi
    have := window_ineq hK (show i + 7 ≤ n by have := List.mem_range.mp hi; omega)
    omega
  rw [isum_map_mul, isum_map_add, isum_map_const, isum_telescope (fun i => winS qD n 6 i K), List.length_range] at hsum
  have hb0 := winS_qD_bound hK (i := 0) (by omega)
  have hb1 := winS_qD_bound hK (i := n - 6) (by omega)
  -- the window sums of the cost count every interior swap ten times
  have hcost : ((List.range (n - 6)).map (fun i => winS (fun J => (cost10 J : Int)) n 7 i K)).sum =
      ((List.range (n - 6)).map (fun i => (adjAt n (0 + i) K : Int))).sum +
        2 * ((List.range (n - 6)).map (fun i => (adjAt n (1 + i) K : Int))).sum +
        2 * ((List.range (n - 6)).map (fun i => (adjAt n (2 + i) K : Int))).sum +
        2 * ((List.range (n - 6)).map (fun i => (adjAt n (3 + i) K : Int))).sum +
        2 * ((List.range (n - 6)).map (fun i => (adjAt n (4 + i) K : Int))).sum +
        ((List.range (n - 6)).map (fun i => (adjAt n (5 + i) K : Int))).sum := by
    rw [isum_congr _ _ _ (fun i hi => winS_cost10 K (show i + 7 ≤ n by have := List.mem_range.mp hi; omega))]
    simp only [isum_map_add, isum_map_mul]
  have s0 := shifted_adj K hn (j := 0) (by decide)
  have s1 := shifted_adj K hn (j := 1) (by decide)
  have s2 := shifted_adj K hn (j := 2) (by decide)
  have s3 := shifted_adj K hn (j := 3) (by decide)
  have s4 := shifted_adj K hn (j := 4) (by decide)
  have s5 := shifted_adj K hn (j := 5) (by decide)
  rw [hcost] at hsum
  have hD : (cD5 : Int) = 1769223456 := rfl
  rw [hD] at hsum
  have hn6 : (((n - 6 : Nat) : Int)) = (n : Int) - 6 := by omega
  rw [hn6, Int.sub_mul] at hsum
  have hc : (0 : Int) ≤ card n K := Int.natCast_nonneg _
  rw [Int.mul_left_comm (n : Int) 11057646600] at hsum
  generalize (n : Int) * card n K = NC at hsum ⊢
  omega

end CDCert.K6
