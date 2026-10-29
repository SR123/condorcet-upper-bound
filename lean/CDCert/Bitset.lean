/-
CDCert.Bitset — Nat bitsets as a kernel-efficient representation of sets of
orders, with proofs that the bit-level generator means exactly what the
list-level one means.

A finite set of orders inside `base` is a natural number `m`: bit `i` says
whether the `i`-th order of `base` is present. Intersection is `&&&`, which the
Lean kernel evaluates with GMP. Measured on n = 4 with all nine options, a
depth-first check over 6,561 leaves takes about 1.3 s this way, whereas the
list-based kernel evaluation of a 733-state enumeration aborts out of memory.

Main results:
* `decode_and_maskOf`: decoding commutes with intersecting by an option mask;
* `decode_runChoice`: decoding a whole run gives `restrict` (hence `domainOf`);
* `exactB_iff`: the bit-level exact-slice test is `ExactSlice` on the decoded
  domain (needs `base.Nodup`, `S ⊆ base`, `S ⊆ E`);
* `pruneB_sound`: the bit-level forbidden-order prune is sound;
* `dfsCheckB_sound`: bit-level checker with required-slice filtering;
* `coverage_of_dfsCheckB`: **transfer** — a successful bit-level kernel check
  proves a property `P` for every defined domain with exact slice `S`, given
  only that a passing leaf decodes to a domain satisfying `P`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Check
import CDCert.Slice

namespace CDCert.Bits

/-! ### Two arithmetic facts -/

theorem eq_iff_mod_two_div_two (a b : Nat) : a = b ↔ a % 2 = b % 2 ∧ a / 2 = b / 2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    omega

theorem mod_two_eq_iff (a b : Nat) : a % 2 = b % 2 ↔ (a % 2 = 1 ↔ b % 2 = 1) := by
  constructor
  · intro h
    rw [h]
  · intro h
    have ha := Nat.mod_two_eq_zero_or_one a
    have hb := Nat.mod_two_eq_zero_or_one b
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb]
    · rw [hb] at h
      have := h.mpr rfl
      omega
    · rw [ha] at h
      have := h.mp rfl
      omega
    · rw [ha, hb]

/-! ### Encoding and decoding -/

section Encode
variable {α : Type}

/-- Bit `i` of `maskOf base p` is `p` applied to the `i`-th order of `base`. -/
def maskOf : List α → (α → Bool) → Nat
  | [], _ => 0
  | x :: xs, p => 2 * maskOf xs p + (if p x then 1 else 0)

/-- The orders of `base` whose bit is set in `m`, in base order. -/
def decode : List α → Nat → List α
  | [], _ => []
  | x :: xs, m => if m % 2 = 1 then x :: decode xs (m / 2) else decode xs (m / 2)

theorem maskOf_cons_mod_two (x : α) (xs : List α) (p : α → Bool) :
    maskOf (x :: xs) p % 2 = 1 ↔ p x = true := by
  simp only [maskOf]
  cases p x <;> simp <;> omega

theorem maskOf_cons_div_two (x : α) (xs : List α) (p : α → Bool) :
    maskOf (x :: xs) p / 2 = maskOf xs p := by
  simp only [maskOf]
  cases p x <;> simp <;> omega

theorem maskOf_lt (base : List α) (p : α → Bool) : maskOf base p < 2 ^ base.length := by
  induction base with
  | nil => simp [maskOf]
  | cons x xs ih =>
    simp only [maskOf, List.length_cons, Nat.pow_succ]
    split <;> omega

/-- Decoding commutes with intersecting by an option mask. -/
theorem decode_and_maskOf (base : List α) (p : α → Bool) (m : Nat) :
    decode base (m &&& maskOf base p) = (decode base m).filter p := by
  induction base generalizing m with
  | nil => rfl
  | cons x xs ih =>
    have hdiv : (m &&& maskOf (x :: xs) p) / 2 = m / 2 &&& maskOf xs p := by
      rw [Nat.and_div_two, maskOf_cons_div_two]
    have hmod : (m &&& maskOf (x :: xs) p) % 2 = 1 ↔ m % 2 = 1 ∧ p x = true := by
      rw [Nat.and_mod_two_eq_one, maskOf_cons_mod_two]
    simp only [decode]
    rw [hdiv, ih]
    by_cases hm : m % 2 = 1 <;> by_cases hp : p x = true
    · rw [if_pos (hmod.mpr ⟨hm, hp⟩), if_pos hm, List.filter_cons, if_pos hp]
    · rw [if_neg (fun h => hp (hmod.mp h).2), if_pos hm, List.filter_cons, if_neg hp]
    · rw [if_neg (fun h => hm (hmod.mp h).1), if_neg hm]
    · rw [if_neg (fun h => hm (hmod.mp h).1), if_neg hm]

/-- The all-ones mask decodes to the whole base. -/
theorem decode_maskOf_true (base : List α) : decode base (maskOf base (fun _ => true)) = base := by
  induction base with
  | nil => rfl
  | cons x xs ih =>
    have h1 : maskOf (x :: xs) (fun _ => true) % 2 = 1 := (maskOf_cons_mod_two x xs _).mpr rfl
    simp only [decode, if_pos h1, maskOf_cons_div_two, ih]

theorem decode_sublist (base : List α) (m : Nat) : (decode base m).Sublist base := by
  induction base generalizing m with
  | nil => exact List.Sublist.slnil
  | cons x xs ih =>
    simp only [decode]
    split
    · exact (ih (m / 2)).cons₂ x
    · exact (ih (m / 2)).cons x

theorem mem_base_of_mem_decode {base : List α} {m : Nat} {x : α} (h : x ∈ decode base m) :
    x ∈ base :=
  (decode_sublist base m).subset h

/-- The head of a duplicate-free base is decoded iff its bit is set. -/
theorem mem_decode_cons_self {x : α} {xs : List α} (hx : x ∉ xs) (m : Nat) :
    x ∈ decode (x :: xs) m ↔ m % 2 = 1 := by
  simp only [decode]
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => List.mem_cons_self⟩
  · rename_i h
    exact ⟨fun hmem => absurd (mem_base_of_mem_decode hmem) hx, fun h' => absurd h' h⟩

/-- Other elements are decoded from the shifted mask. -/
theorem mem_decode_cons_of_ne {x y : α} {xs : List α} (hy : y ≠ x) (m : Nat) :
    y ∈ decode (x :: xs) m ↔ y ∈ decode xs (m / 2) := by
  simp only [decode]
  split
  · rw [List.mem_cons]
    exact ⟨fun h => h.resolve_left hy, Or.inr⟩
  · exact Iff.rfl

/-- Number of set bits among the lowest `k` bits. -/
def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, m => m % 2 + countBits k (m / 2)

theorem length_decode (base : List α) (m : Nat) :
    (decode base m).length = countBits base.length m := by
  induction base generalizing m with
  | nil => rfl
  | cons x xs ih =>
    simp only [decode, countBits, List.length_cons]
    split
    · rename_i h
      rw [List.length_cons, ih, h]
      omega
    · rename_i h
      rw [ih]
      omega

end Encode

/-! ### The bit-level action and its simulation of filtering -/

/-- Intersect a state with an option mask. -/
def andAct (k m : Nat) : Nat := m &&& k

section Simulation
variable {α : Type}

/-- **Simulation.** Decoding a bit-level run gives the list-level restriction. -/
theorem decode_runChoice (base : List α) (c : List (Opt α)) (m : Nat) :
    decode base (runChoice andAct m (c.map (maskOf base))) = restrict (decode base m) c := by
  rw [runChoice_sim (fun o (D : List α) => D.filter o) andAct (decode base) (maskOf base)
    (fun o s => decode_and_maskOf base o s) c m]
  exact runChoice_filter _ c

/-- Starting from the all-ones mask, a bit-level run decodes to `domainOf`. -/
theorem decode_runChoice_full (base : List α) (c : List (Opt α)) :
    decode base (runChoice andAct (maskOf base (fun _ => true)) (c.map (maskOf base))) =
      domainOf base c := by
  rw [decode_runChoice, decode_maskOf_true]
  rfl

end Simulation

/-! ### Bit-level slice tests -/

/-- `a` is a bitwise subset of `b`. -/
def subB (a b : Nat) : Bool := (a &&& b) == a

/-- Required slice at bit level: keep the option masks containing `sM`. -/
def requireSliceB (sM : Nat) (gs : List (List Nat)) : List (List Nat) :=
  gs.map (List.filter (subB sM))

/-- Exact slice at bit level: the `eM`-part of `m` is exactly `sM`. -/
def exactB (eM sM m : Nat) : Bool := (m &&& eM) == sM

/-- Intersect `x` with every option mask of every remaining group. -/
def retainAll (gs : List (List Nat)) (x : Nat) : Nat :=
  gs.foldl (fun acc g => g.foldl (fun a k => a &&& k) acc) x

/-- Forbidden endpoint orders: in `eM` but not in `sM`. -/
def forbiddenMask (eM sM : Nat) : Nat := eM ^^^ (eM &&& sM)

/-- Bit-level prune: some forbidden order is present and kept by every option
of every remaining group. -/
def pruneB (fM : Nat) (gs : List (List Nat)) (m : Nat) : Bool := retainAll gs (m &&& fM) != 0

theorem testBit_runChoice_andAct (i : Nat) :
    ∀ (c : List Nat) (m : Nat),
      (runChoice andAct m c).testBit i = (m.testBit i && c.all (fun k => k.testBit i)) := by
  intro c
  induction c with
  | nil => intro m; simp [runChoice]
  | cons k c ih =>
    intro m
    simp only [runChoice, andAct]
    rw [ih, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem testBit_foldl_and (i : Nat) :
    ∀ (g : List Nat) (x : Nat),
      (g.foldl (fun a k => a &&& k) x).testBit i = (x.testBit i && g.all (fun k => k.testBit i)) := by
  intro g
  induction g with
  | nil => intro x; simp
  | cons k g ih =>
    intro x
    simp only [List.foldl_cons]
    rw [ih, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem testBit_retainAll (i : Nat) :
    ∀ (gs : List (List Nat)) (x : Nat),
      (retainAll gs x).testBit i =
        (x.testBit i && gs.all (fun g => g.all (fun k => k.testBit i))) := by
  intro gs
  induction gs with
  | nil => intro x; simp [retainAll]
  | cons g gs ih =>
    intro x
    have h := ih (g.foldl (fun a k => a &&& k) x)
    simp only [retainAll, List.foldl_cons] at h ⊢
    rw [h, testBit_foldl_and, List.all_cons, Bool.and_assoc]

theorem testBit_forbiddenMask (eM sM i : Nat) :
    (forbiddenMask eM sM).testBit i = (eM.testBit i && !sM.testBit i) := by
  simp only [forbiddenMask, Nat.testBit_xor, Nat.testBit_and]
  cases eM.testBit i <;> cases sM.testBit i <;> rfl

/-- **Bit-level prune soundness.** -/
theorem pruneB_sound (eM sM : Nat) :
    PruneSoundFor andAct (pruneB (forbiddenMask eM sM)) (exactB eM sM) := by
  intro gs m hp c hc
  have hne : retainAll gs (m &&& forbiddenMask eM sM) ≠ 0 := by
    simpa [pruneB] using hp
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  rw [testBit_retainAll, Nat.testBit_and, testBit_forbiddenMask] at hi
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hi
  obtain ⟨⟨hm, heM, hsM⟩, hall⟩ := hi
  have hr : (runChoice andAct m c).testBit i = true := by
    rw [testBit_runChoice_andAct, hm, Bool.true_and, List.all_eq_true]
    intro k hk
    obtain ⟨g, hg, hkg⟩ := hc.exists_group k hk
    exact hall g hg k hkg
  cases h : exactB eM sM (runChoice andAct m c) with
  | false => rfl
  | true =>
    have heq : (runChoice andAct m c &&& eM) = sM := by simpa [exactB] using h
    have := congrArg (fun x => x.testBit i) heq
    simp only [Nat.testBit_and, hr, heM, hsM, Bool.true_and] at this
    cases this

/-- Every option of a choice whose result has exact slice `sM` contains `sM`. -/
theorem subB_of_exactB {eM sM m : Nat} {c : List Nat}
    (h : exactB eM sM (runChoice andAct m c) = true) : ∀ k, k ∈ c → subB sM k = true := by
  intro k hk
  have heq : (runChoice andAct m c &&& eM) = sM := by simpa [exactB] using h
  simp only [subB, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases hs : sM.testBit i with
  | false => rfl
  | true =>
    have h1 := congrArg (fun x => x.testBit i) heq
    simp only [Nat.testBit_and, hs, Bool.and_eq_true] at h1
    rw [testBit_runChoice_andAct, Bool.and_eq_true, List.all_eq_true] at h1
    rw [Bool.true_and]
    exact h1.1.2 k hk

/-- **Bit-level checker with required-slice filtering.** -/
theorem dfsCheckB_sound (eM sM : Nat) (leafOK : Nat → Bool) (gs : List (List Nat)) (m0 : Nat)
    (h : dfsCheck andAct (pruneB (forbiddenMask eM sM)) leafOK (requireSliceB sM gs) m0 = true) :
    ∀ c, IsChoice c gs → exactB eM sM (runChoice andAct m0 c) = true →
      leafOK (runChoice andAct m0 c) = true := by
  intro c hc hx
  have hc' : IsChoice c (requireSliceB sM gs) :=
    IsChoice.filter (subB sM) hc (subB_of_exactB hx)
  exact dfsCheck_sound (pruneB_sound eM sM) _ m0 h c hc' hx

/-! ### Exactness transfer (needs a duplicate-free base) -/

section Transfer
variable {α : Type}

/-- Position-wise agreement: at each position, bit of `m` and `p` together equal `q`. -/
def Agree : List α → Nat → (α → Bool) → (α → Bool) → Prop
  | [], _, _, _ => True
  | x :: xs, m, p, q => ((m % 2 = 1 ∧ p x = true) ↔ q x = true) ∧ Agree xs (m / 2) p q

theorem and_maskOf_eq_maskOf_iff (base : List α) (p q : α → Bool) (m : Nat) :
    (m &&& maskOf base p) = maskOf base q ↔ Agree base m p q := by
  induction base generalizing m with
  | nil => simp [maskOf, Agree, Nat.and_zero]
  | cons x xs ih =>
    rw [eq_iff_mod_two_div_two, mod_two_eq_iff, Nat.and_mod_two_eq_one, Nat.and_div_two,
      maskOf_cons_mod_two, maskOf_cons_mod_two, maskOf_cons_div_two, maskOf_cons_div_two, ih]
    rfl

theorem agree_iff_of_nodup {base : List α} (hnd : base.Nodup) (p q : α → Bool) (m : Nat) :
    Agree base m p q ↔ ∀ x, x ∈ base → ((x ∈ decode base m ∧ p x = true) ↔ q x = true) := by
  induction base generalizing m with
  | nil => simp [Agree]
  | cons x xs ih =>
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [Agree]
    rw [ih hnd' (m / 2)]
    constructor
    · rintro ⟨h0, hrest⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [mem_decode_cons_self hx m]
        exact h0
      · have hyx : y ≠ x := fun h => hx (h ▸ hy)
        rw [mem_decode_cons_of_ne hyx]
        exact hrest y hy
    · intro h
      refine ⟨?_, fun y hy => ?_⟩
      · have := h x List.mem_cons_self
        rwa [mem_decode_cons_self hx m] at this
      · have hyx : y ≠ x := fun h => hx (h ▸ hy)
        have := h y (List.mem_cons_of_mem _ hy)
        rwa [mem_decode_cons_of_ne hyx] at this

/-- **Exactness transfer.** The bit-level exact-slice test on `m` is
`ExactSlice` on the decoded set of orders. -/
theorem exactB_iff [DecidableEq α] {base : List α} (hnd : base.Nodup) {E : α → Bool}
    {S : List α} (hSb : ∀ s, s ∈ S → s ∈ base) (hSE : ∀ s, s ∈ S → E s = true) (m : Nat) :
    exactB (maskOf base E) (maskOf base (optOfList S)) m = true ↔
      ExactSlice E S (decode base m) := by
  rw [exactSlice_iff hSE]
  simp only [exactB, beq_iff_eq]
  rw [and_maskOf_eq_maskOf_iff, agree_iff_of_nodup hnd]
  simp only [optOfList_eq_true]
  constructor
  · intro h x
    by_cases hx : x ∈ base
    · exact h x hx
    · exact ⟨fun h' => absurd (mem_base_of_mem_decode h'.1) hx, fun h' => absurd (hSb x h') hx⟩
  · intro h x _
    exact h x

/-- **Transfer theorem.** A successful bit-level kernel check proves `P` for
every domain defined by a choice for `gs` whose `E`-slice is exactly `S`,
provided every passing leaf decodes to a domain satisfying `P`. -/
theorem coverage_of_dfsCheckB [DecidableEq α] {base : List α} (hnd : base.Nodup)
    (gs : List (Group α)) (E : α → Bool) (S : List α)
    (hSb : ∀ s, s ∈ S → s ∈ base) (hSE : ∀ s, s ∈ S → E s = true)
    (leafOK : Nat → Bool) (P : List α → Prop)
    (hleaf : ∀ m, leafOK m = true → P (decode base m))
    (h : dfsCheck andAct (pruneB (forbiddenMask (maskOf base E) (maskOf base (optOfList S))))
          leafOK (requireSliceB (maskOf base (optOfList S)) (gs.map (List.map (maskOf base))))
          (maskOf base (fun _ => true)) = true) :
    ∀ c, IsChoice c gs → ExactSlice E S (domainOf base c) → P (domainOf base c) := by
  intro c hc hx
  have hcB := hc.map (maskOf base)
  have hdec := decode_runChoice_full base c
  have hxB : exactB (maskOf base E) (maskOf base (optOfList S))
      (runChoice andAct (maskOf base (fun _ => true)) (c.map (maskOf base))) = true := by
    rw [exactB_iff hnd hSb hSE, hdec]
    exact hx
  have hl := dfsCheckB_sound _ _ leafOK _ _ h _ hcB hxB
  rw [← hdec]
  exact hleaf _ hl

/-- The same without slices: a successful bit-level check (no pruning) proves
`P` for every defined domain. -/
theorem coverage_of_dfsCheckB_noPrune {base : List α} (gs : List (Group α))
    (leafOK : Nat → Bool) (P : List α → Prop)
    (hleaf : ∀ m, leafOK m = true → P (decode base m))
    (h : dfsCheck andAct (fun _ _ => false) leafOK (gs.map (List.map (maskOf base)))
          (maskOf base (fun _ => true)) = true) :
    ∀ c, IsChoice c gs → P (domainOf base c) := by
  intro c hc
  have hl := (dfsCheck_noPrune_iff _ _).mp h _ (hc.map (maskOf base))
  rw [← decode_runChoice_full base c]
  exact hleaf _ hl

end Transfer

end CDCert.Bits
