/-
CDCert.Supermult — **ordered concatenation of semantic Condorcet domains** and the
supermultiplicativity of the extremal functions:

  `f_supermul : f m * f n ≤ f (m + n)`,  `h_supermul : h m * h n ≤ h (m + n)`,
  `one_le_f : 1 ≤ f n`,  `one_le_h : 1 ≤ h n`.

`catOrder r s` puts the alternatives `0, …, m-1` (ordered by `r`) above `m, …, m+n-1` (ordered by
`s`). For an odd profile of concatenated orders the majority on a block is the majority of the
block profile, and every cross-block comparison is unanimous, so concatenation preserves the
semantic Condorcet property (every odd profile has a transitive majority); a crossing triple has
its lone alternative always first or always last, so concatenation also preserves extreme laws.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import Condorcet.Extremal

namespace CDCert.Supermult

open Condorcet

variable {m n : Nat}

/-! ### Concatenated orders -/

/-- Ordered concatenation of comparison relations. -/
def catRel (r : Order (Fin m)) (s : Order (Fin n)) (a b : Fin (m + n)) : Bool :=
  if ha : a.val < m then
    if hb : b.val < m then r ⟨a.val, ha⟩ ⟨b.val, hb⟩ else true
  else
    if hb : b.val < m then false
    else s ⟨a.val - m, by have := a.isLt; omega⟩ ⟨b.val - m, by have := b.isLt; omega⟩

section
variable (r : Order (Fin m)) (s : Order (Fin n))

@[simp] theorem catRel_cc (a b : Fin m) : catRel r s (Fin.castAdd n a) (Fin.castAdd n b) = r a b := by
  unfold catRel
  rw [dif_pos (by simp), dif_pos (by simp)]
  rfl

@[simp] theorem catRel_cn (a : Fin m) (b : Fin n) : catRel r s (Fin.castAdd n a) (Fin.natAdd m b) = true := by
  unfold catRel
  rw [dif_pos (by simp), dif_neg (by simp)]

@[simp] theorem catRel_nc (a : Fin n) (b : Fin m) : catRel r s (Fin.natAdd m a) (Fin.castAdd n b) = false := by
  unfold catRel
  rw [dif_neg (by simp), dif_pos (by simp)]

@[simp] theorem catRel_nn (a b : Fin n) : catRel r s (Fin.natAdd m a) (Fin.natAdd m b) = s a b := by
  unfold catRel
  rw [dif_neg (by simp), dif_neg (by simp)]
  have e : ∀ (x : Fin n) (hx : (Fin.natAdd m x).val - m < n), (⟨(Fin.natAdd m x).val - m, hx⟩ : Fin n) = x :=
    fun x hx => Fin.ext (by simp)
  rw [e a, e b]

theorem catRel_strict : IsStrictTotal (catRel r s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    induction a using Fin.addCases with
    | left a => rw [catRel_cc]; exact r.irrefl a
    | right a => rw [catRel_nn]; exact s.irrefl a
  · intro a b c hab hbc
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      induction c using Fin.addCases <;> simp_all
    · exact r.trans hab hbc
    · exact s.trans hab hbc
  · intro a b hne
    induction a using Fin.addCases <;> induction b using Fin.addCases <;> simp only [catRel_cc,
      catRel_cn, catRel_nc, catRel_nn, true_or, or_true]
    · exact r.total (fun h => hne (by rw [h]))
    · exact s.total (fun h => hne (by rw [h]))

end

/-- The concatenated order. -/
def catOrder (r : Order (Fin m)) (s : Order (Fin n)) : Order (Fin (m + n)) :=
  ⟨catRel r s, catRel_strict r s⟩

@[simp] theorem catOrder_apply (r : Order (Fin m)) (s : Order (Fin n)) (a b : Fin (m + n)) :
    catOrder r s a b = catRel r s a b := rfl

theorem catOrder_injective :
    Function.Injective (fun p : Order (Fin m) × Order (Fin n) => catOrder p.1 p.2) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  have hv : ∀ a b, catRel r s a b = catRel r' s' a b := fun a b =>
    congrArg (fun o : Order (Fin (m + n)) => o a b) h
  have h1 : r = r' := Order.ext (fun a b => by simpa using hv (Fin.castAdd n a) (Fin.castAdd n b))
  have h2 : s = s' := Order.ext (fun a b => by simpa using hv (Fin.natAdd m a) (Fin.natAdd m b))
  rw [h1, h2]

/-! ### Concatenated domains -/

/-- The ordered concatenation of two domains. -/
noncomputable def catDomain (D : Domain (Fin m)) (E : Domain (Fin n)) : Domain (Fin (m + n)) :=
  (D ×ˢ E).image (fun p => catOrder p.1 p.2)

theorem mem_catDomain {D : Domain (Fin m)} {E : Domain (Fin n)} {o : Order (Fin (m + n))} :
    o ∈ catDomain D E ↔ ∃ r ∈ D, ∃ s ∈ E, catOrder r s = o := by
  unfold catDomain
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨r, s⟩, hp, rfl⟩
    rw [Finset.mem_product] at hp
    exact ⟨r, hp.1, s, hp.2, rfl⟩
  · rintro ⟨r, hr, s, hs, rfl⟩
    exact ⟨(r, s), Finset.mem_product.mpr ⟨hr, hs⟩, rfl⟩

theorem card_catDomain (D : Domain (Fin m)) (E : Domain (Fin n)) :
    (catDomain D E).card = D.card * E.card := by
  unfold catDomain
  rw [Finset.card_image_of_injective _ catOrder_injective, Finset.card_product]

/-! ### Majorities -/

theorem majority_congr {α β : Type*} {k : Nat} (v : Fin k → Order α) (w : Fin k → Order β)
    {a b : α} {c d : β} (h : ∀ i, v i a b = w i c d) : majority v a b ↔ majority w c d := by
  unfold majority
  have e : Finset.univ.filter (fun i => v i a b = true) = Finset.univ.filter (fun i => w i c d = true) := by
    ext i; simp [h i]
  rw [e]

theorem majority_of_all {α : Type*} {k : Nat} (hk : 0 < k) (v : Fin k → Order α) {a b : α}
    (h : ∀ i, v i a b = true) : majority v a b := by
  unfold majority
  rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ, Fintype.card_fin]
  omega

theorem not_majority_of_none {α : Type*} {k : Nat} (v : Fin k → Order α) {a b : α}
    (h : ∀ i, v i a b = false) : ¬ majority v a b := by
  unfold majority
  rw [Finset.filter_false_of_mem (fun i _ => by simp [h i])]
  simp

/-- **Concatenation preserves the semantic Condorcet property.** -/
theorem catDomain_isCondorcet {D : Domain (Fin m)} {E : Domain (Fin n)} (hD : IsCondorcet D)
    (hE : IsCondorcet E) : IsCondorcet (catDomain D E) := by
  intro k hk v hv
  have hc : ∀ i, ∃ p : Order (Fin m) × Order (Fin n), p.1 ∈ D ∧ p.2 ∈ E ∧ catOrder p.1 p.2 = v i := by
    intro i
    obtain ⟨r, hr, s, hs, he⟩ := mem_catDomain.mp (hv i)
    exact ⟨(r, s), hr, hs, he⟩
  choose p hp1 hp2 hp3 using hc
  have tR := hD k hk (fun i => (p i).1) hp1
  have tS := hE k hk (fun i => (p i).2) hp2
  have hval : ∀ i a b, v i a b = catRel (p i).1 (p i).2 a b := fun i a b => by rw [← hp3 i]; rfl
  have hk0 : 0 < k := by obtain ⟨j, hj⟩ := hk; omega
  intro a b c hab hbc
  induction a using Fin.addCases with
  | left a =>
    induction c using Fin.addCases with
    | left c =>
      induction b using Fin.addCases with
      | left b =>
        have e1 := majority_congr v (fun i => (p i).1) (a := Fin.castAdd n a) (b := Fin.castAdd n b)
          (c := a) (d := b) (fun i => by rw [hval]; simp)
        have e2 := majority_congr v (fun i => (p i).1) (a := Fin.castAdd n b) (b := Fin.castAdd n c)
          (c := b) (d := c) (fun i => by rw [hval]; simp)
        have e3 := majority_congr v (fun i => (p i).1) (a := Fin.castAdd n a) (b := Fin.castAdd n c)
          (c := a) (d := c) (fun i => by rw [hval]; simp)
        exact e3.mpr (tR (e1.mp hab) (e2.mp hbc))
      | right b =>
        exact absurd hbc (not_majority_of_none v (fun i => by rw [hval]; simp))
    | right c => exact majority_of_all hk0 v (fun i => by rw [hval]; simp)
  | right a =>
    induction c using Fin.addCases with
    | left c =>
      induction b using Fin.addCases with
      | left b => exact absurd hab (not_majority_of_none v (fun i => by rw [hval]; simp))
      | right b => exact absurd hbc (not_majority_of_none v (fun i => by rw [hval]; simp))
    | right c =>
      induction b using Fin.addCases with
      | left b => exact absurd hab (not_majority_of_none v (fun i => by rw [hval]; simp))
      | right b =>
        have e1 := majority_congr v (fun i => (p i).2) (a := Fin.natAdd m a) (b := Fin.natAdd m b)
          (c := a) (d := b) (fun i => by rw [hval]; simp)
        have e2 := majority_congr v (fun i => (p i).2) (a := Fin.natAdd m b) (b := Fin.natAdd m c)
          (c := b) (d := c) (fun i => by rw [hval]; simp)
        have e3 := majority_congr v (fun i => (p i).2) (a := Fin.natAdd m a) (b := Fin.natAdd m c)
          (c := a) (d := c) (fun i => by rw [hval]; simp)
        exact e3.mpr (tS (e1.mp hab) (e2.mp hbc))

/-! ### Extreme laws -/

theorem never_zero {α : Type*} (r : Order α) (x y z : α) :
    Never r x y z 0 ↔ (r x y = false ∨ r x z = false) := by
  simp [Never]

theorem never_two {α : Type*} (r : Order α) (x y z : α) :
    Never r x y z 2 ↔ (r x y = true ∨ r x z = true) := by
  simp [Never]

theorem never_cc (r : Order (Fin m)) (s : Order (Fin n)) (x y z : Fin m) (p : Fin 3) :
    Never (catOrder r s) (Fin.castAdd n x) (Fin.castAdd n y) (Fin.castAdd n z) p ↔ Never r x y z p := by
  unfold Never
  simp only [catOrder_apply, catRel_cc]

theorem never_nn (r : Order (Fin m)) (s : Order (Fin n)) (x y z : Fin n) (p : Fin 3) :
    Never (catOrder r s) (Fin.natAdd m x) (Fin.natAdd m y) (Fin.natAdd m z) p ↔ Never s x y z p := by
  unfold Never
  simp only [catOrder_apply, catRel_nn]

/-- **Concatenation preserves extreme laws.** -/
theorem catDomain_extremeRestricted {D : Domain (Fin m)} {E : Domain (Fin n)}
    (hD : ExtremeRestricted D) (hE : ExtremeRestricted E) : ExtremeRestricted (catDomain D E) := by
  intro a b c hab hac hbc
  -- a lone alternative of a crossing triple is always last (never first, law `0`) or always first
  -- (never last, law `2`)
  have low : ∀ x y z : Fin (m + n), (∀ o ∈ catDomain D E, o x y = false) → (∀ o ∈ catDomain D E, Never o x y z 0) :=
    fun x y z h o ho => (never_zero o x y z).mpr (Or.inl (h o ho))
  have high : ∀ x y z : Fin (m + n), (∀ o ∈ catDomain D E, o x y = true) → (∀ o ∈ catDomain D E, Never o x y z 2) :=
    fun x y z h o ho => (never_two o x y z).mpr (Or.inl (h o ho))
  have z2 : (0 : Fin 3) ≠ 1 := by decide
  have t2 : (2 : Fin 3) ≠ 1 := by decide
  induction a using Fin.addCases with
  | left a =>
    induction b using Fin.addCases with
    | left b =>
      induction c using Fin.addCases with
      | left c =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        have hac' : a ≠ c := fun h => hac (by rw [h])
        have hbc' : b ≠ c := fun h => hbc (by rw [h])
        obtain ⟨q, hq, hcases⟩ := hD a b c hab' hac' hbc'
        refine ⟨q, hq, ?_⟩
        rcases hcases with h1 | h1 | h1
        · left; intro o ho
          obtain ⟨r, hr, s, -, rfl⟩ := mem_catDomain.mp ho
          exact (never_cc r s a b c q).mpr (h1 r hr)
        · right; left; intro o ho
          obtain ⟨r, hr, s, -, rfl⟩ := mem_catDomain.mp ho
          exact (never_cc r s b a c q).mpr (h1 r hr)
        · right; right; intro o ho
          obtain ⟨r, hr, s, -, rfl⟩ := mem_catDomain.mp ho
          exact (never_cc r s c a b q).mpr (h1 r hr)
      | right c =>
        refine ⟨0, z2, Or.inr (Or.inr (low _ _ _ (fun o ho => ?_)))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
    | right b =>
      induction c using Fin.addCases with
      | left c =>
        refine ⟨0, z2, Or.inr (Or.inl (low _ _ _ (fun o ho => ?_)))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
      | right c =>
        refine ⟨2, t2, Or.inl (high _ _ _ (fun o ho => ?_))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
  | right a =>
    induction b using Fin.addCases with
    | left b =>
      induction c using Fin.addCases with
      | left c =>
        refine ⟨0, z2, Or.inl (low _ _ _ (fun o ho => ?_))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
      | right c =>
        refine ⟨2, t2, Or.inr (Or.inl (high _ _ _ (fun o ho => ?_)))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
    | right b =>
      induction c using Fin.addCases with
      | left c =>
        refine ⟨2, t2, Or.inr (Or.inr (high _ _ _ (fun o ho => ?_)))⟩
        obtain ⟨r, -, s, -, rfl⟩ := mem_catDomain.mp ho
        simp
      | right c =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        have hac' : a ≠ c := fun h => hac (by rw [h])
        have hbc' : b ≠ c := fun h => hbc (by rw [h])
        obtain ⟨q, hq, hcases⟩ := hE a b c hab' hac' hbc'
        refine ⟨q, hq, ?_⟩
        rcases hcases with h1 | h1 | h1
        · left; intro o ho
          obtain ⟨r, -, s, hs, rfl⟩ := mem_catDomain.mp ho
          exact (never_nn r s a b c q).mpr (h1 s hs)
        · right; left; intro o ho
          obtain ⟨r, -, s, hs, rfl⟩ := mem_catDomain.mp ho
          exact (never_nn r s b a c q).mpr (h1 s hs)
        · right; right; intro o ho
          obtain ⟨r, -, s, hs, rfl⟩ := mem_catDomain.mp ho
          exact (never_nn r s c a b q).mpr (h1 s hs)

theorem catDomain_isPeakPit {D : Domain (Fin m)} {E : Domain (Fin n)} (hD : IsPeakPit D)
    (hE : IsPeakPit E) : IsPeakPit (catDomain D E) :=
  ⟨catDomain_isCondorcet hD.1 hE.1, catDomain_extremeRestricted hD.2 hE.2⟩

/-! ### Supermultiplicativity -/

/-- **`f` is supermultiplicative.** -/
theorem f_supermul (m n : Nat) : f m * f n ≤ f (m + n) := by
  obtain ⟨D, hD, hDc⟩ := exists_maximum_general m
  obtain ⟨E, hE, hEc⟩ := exists_maximum_general n
  rw [← hDc, ← hEc, ← card_catDomain]
  exact card_le_f (catDomain_isCondorcet hD hE)

/-- **`h` is supermultiplicative.** -/
theorem h_supermul (m n : Nat) : h m * h n ≤ h (m + n) := by
  obtain ⟨D, hD, hDc⟩ := exists_maximum_peakPit m
  obtain ⟨E, hE, hEc⟩ := exists_maximum_peakPit n
  rw [← hDc, ← hEc, ← card_catDomain]
  exact card_le_h (catDomain_isPeakPit hD hE)

/-! ### A single order -/

/-- The order `0 > 1 > ⋯` on `Fin n` (smaller labels above). -/
def natOrder (n : Nat) : Order (Fin n) :=
  ⟨fun a b => decide (a.val < b.val),
    ⟨fun a => by simp, fun a b c h1 h2 => by simp at h1 h2 ⊢; omega,
      fun a b h => by
        have : a.val ≠ b.val := fun e => h (Fin.ext e)
        by_cases hab : a.val < b.val
        · left; simpa using hab
        · right; simp; omega⟩⟩

theorem singleton_isCondorcet {α : Type*} (r : Order α) : IsCondorcet ({r} : Domain α) := by
  intro k hk v hv
  have hvr : ∀ i, v i = r := fun i => Finset.mem_singleton.mp (hv i)
  have hk0 : 0 < k := by obtain ⟨j, hj⟩ := hk; omega
  have key : ∀ a b, majority v a b ↔ r a b = true := by
    intro a b
    constructor
    · intro hm
      by_contra hne
      exact not_majority_of_none v (fun i => by rw [hvr i]; simpa using hne) hm
    · intro hr
      exact majority_of_all hk0 v (fun i => by rw [hvr i]; exact hr)
  intro a b c hab hbc
  exact (key a c).mpr (r.trans ((key a b).mp hab) ((key b c).mp hbc))

theorem singleton_extremeRestricted {α : Type*} (r : Order α) : ExtremeRestricted ({r} : Domain α) := by
  intro a b c _ _ _
  refine ⟨0, by decide, ?_⟩
  by_cases h : r a b = false ∨ r a c = false
  · left
    intro o ho
    rw [Finset.mem_singleton.mp ho]
    exact (never_zero r a b c).mpr h
  · right; left
    intro o ho
    rw [Finset.mem_singleton.mp ho]
    have hab : r a b = true := by
      cases e : r a b
      · exact absurd (Or.inl e) h
      · rfl
    exact (never_zero r b a c).mpr (Or.inl (r.asymmetric hab))

theorem one_le_f (n : Nat) : 1 ≤ f n := by
  have := card_le_f (singleton_isCondorcet (natOrder n))
  simpa using this

theorem one_le_h (n : Nat) : 1 ≤ h n := by
  have := card_le_h ⟨singleton_isCondorcet (natOrder n), singleton_extremeRestricted (natOrder n)⟩
  simpa using this

end CDCert.Supermult
