/-
CDCert.FreeLocked — **the free-to-locked injection** (Proposition `prop:free`): for every maximal
Condorcet domain `D`, `freeCount D ≤ lockedCount D`, in Codex's counts.

Following the paper (Moros's injection, Lemmas `lem:adj`, `lem:pull`): for a free pair `(σ, b)`
let `a`, `c` be the alternatives directly above and below `b` in `σ`, `T = {a, b, c}`.

* `pull_law`: `D` satisfies "`a` never last" or "`c` never first" on `T` (the orders `σ`, a lift and
  a drop of `b` give `abc`, `bac`, `acb` on `T`);
* `not_both`: for maximal `D`, not both (else `a` is above `c` in every order while a lift of `b`
  has `a` directly above `c`, against Codex's `IsMaximal.fixed_pair_not_consecutive`);
* `ψ(σ, b) = (τ, rank_τ a)` where `τ` is a lift of `b` if `D` satisfies "`a` never last" on `T`, and a
  drop otherwise; the letter `(a, c)` of `τ` is locked (`psi_locked`);
* `psi_injective`: the three cases "both upper", "both lower", "mixed" of the paper, each reduced
  to a finite statement about the patterns of a few orders on a triple, decided by `decide`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import Condorcet.GapCounts
import Condorcet.TripleCharacterization
import CDCert.Supermult

namespace CDCert.FreeLocked

open Condorcet

instance instNonemptyOrderFin (m : Nat) : Nonempty (Order (Fin m)) := ⟨CDCert.Supermult.natOrder m⟩

/-! ### Moving one alternative -/

section Cross
variable {α : Type*} [Fintype α]

/-- If `σ`, `τ` agree off `b`, `b` is above `x` in `σ` and below `x` in `τ`, then `b` is strictly
higher in `σ`. -/
theorem rank_lt_of_cross {σ τ : Order α} {b x : α}
    (hagree : ∀ y z, y ≠ b → z ≠ b → σ y z = τ y z) (hx : x ≠ b)
    (h1 : σ b x = true) (h2 : τ x b = true) : σ.rank b < τ.rank b := by
  classical
  unfold Order.rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, (Order.mem_above τ x b).mpr h2, ?_⟩
    rw [Order.mem_above, σ.asymmetric h1]
    simp
  · intro y hy
    rw [Order.mem_above] at hy ⊢
    have hyb : y ≠ b := by
      rintro rfl
      rw [σ.irrefl] at hy
      contradiction
    have hyx : σ y x = true := σ.trans hy h1
    have hyx' : τ y x = true := by rw [← hagree y x hyb hx]; exact hyx
    exact τ.trans hyx' h2

end Cross

variable {n : Nat}

/-- Two orders agree off `b`. -/
def AgreeOff (σ τ : Order (Fin (n + 1))) (b : Fin (n + 1)) : Prop :=
  ∀ y z, y ≠ b → z ≠ b → σ y z = τ y z

theorem agreeOff_of_deleted {σ τ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : deletedOrder b τ = deletedOrder b σ) : AgreeOff σ τ b :=
  fun _ _ hy hz => (deletedOrder_eq_comparisons b h hy hz).symm

theorem AgreeOff.symm {σ τ : Order (Fin (n + 1))} {b : Fin (n + 1)} (h : AgreeOff σ τ b) :
    AgreeOff τ σ b := fun y z hy hz => (h y z hy hz).symm

/-- A lift keeps the alternatives below `b` below it. -/
theorem lift_keeps_below {σ τ : Order (Fin (n + 1))} {b x : Fin (n + 1)} (hag : AgreeOff σ τ b)
    (hr : τ.rank b < σ.rank b) (hx : x ≠ b) (h : σ b x = true) : τ b x = true := by
  by_contra hc
  have h2 : τ x b = true := (τ.total hx).resolve_right hc
  have := rank_lt_of_cross hag hx h h2
  omega

/-- A drop keeps the alternatives above `b` above it. -/
theorem drop_keeps_above {σ τ : Order (Fin (n + 1))} {b x : Fin (n + 1)} (hag : AgreeOff σ τ b)
    (hr : σ.rank b < τ.rank b) (hx : x ≠ b) (h : σ x b = true) : τ x b = true := by
  by_contra hc
  have h2 : τ b x = true := (τ.total hx.symm).resolve_right hc
  have := rank_lt_of_cross hag.symm hx h2 h
  omega

/-- Lifts in rank form. -/
theorem lift_data {D : Domain (Fin (n + 1))} {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : HasLift D σ b) : ∃ τ ∈ D, deletedOrder b τ = deletedOrder b σ ∧ orderSlot b τ < orderSlot b σ :=
  h

theorem rank_lt_of_slot_lt {σ τ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : orderSlot b τ < orderSlot b σ) : τ.rank b < σ.rank b := by
  rw [Fin.lt_def, orderSlot_val_eq_rank, orderSlot_val_eq_rank] at h
  exact h

/-! ### Neighbours -/

theorem exists_up_of_hasLift {D : Domain (Fin (n + 1))} {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : HasLift D σ b) : ∃ a, σ.Consecutive a b := by
  have hb := σ.rank_lt_size b
  simp only [Fintype.card_fin] at hb
  have h1 : 1 ≤ σ.rank b := by
    by_contra h0
    have hz : σ.rank b = 0 := by omega
    have : σ.atPos 0 = b := σ.rank_injective (by rw [Order.rank_atPos, hz]; rfl)
    exact top_has_no_lift D σ (this ▸ h)
  let j : Fin n := ⟨σ.rank b - 1, by omega⟩
  refine ⟨σ.atPos j.castSucc, ?_⟩
  have hjb : σ.atPos j.succ = b := σ.rank_injective (by
    rw [Order.rank_atPos]; simp only [Fin.val_succ, j]; omega)
  have hc := σ.atPos_consecutive j
  rw [hjb] at hc
  exact hc

theorem exists_down_of_hasDrop {D : Domain (Fin (n + 1))} {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : HasDrop D σ b) : ∃ c, σ.Consecutive b c := by
  have hb := σ.rank_lt_size b
  simp only [Fintype.card_fin] at hb
  have h1 : σ.rank b < n := by
    by_contra h0
    have hz : σ.rank b = n := by omega
    have : σ.atPos (Fin.last n) = b := σ.rank_injective (by rw [Order.rank_atPos, hz]; rfl)
    exact bottom_has_no_drop D σ (this ▸ h)
  let j : Fin n := ⟨σ.rank b, h1⟩
  refine ⟨σ.atPos j.succ, ?_⟩
  have hjb : σ.atPos j.castSucc = b := σ.rank_injective (by
    rw [Order.rank_atPos]; simp only [Fin.val_castSucc, j])
  have hc := σ.atPos_consecutive j
  rw [hjb] at hc
  exact hc

theorem up_unique {σ : Order (Fin (n + 1))} {a a' b : Fin (n + 1)} (h : σ.Consecutive a b)
    (h' : σ.Consecutive a' b) : a = a' := by
  have e1 := h.rank_succ
  have e2 := h'.rank_succ
  exact σ.rank_injective (by omega)

theorem down_unique {σ : Order (Fin (n + 1))} {b c c' : Fin (n + 1)} (h : σ.Consecutive b c)
    (h' : σ.Consecutive b c') : c = c' := by
  have e1 := h.rank_succ
  have e2 := h'.rank_succ
  exact σ.rank_injective (by omega)

/-- The alternative directly above `b` (arbitrary when there is none). -/
noncomputable def upN (σ : Order (Fin (n + 1))) (b : Fin (n + 1)) : Fin (n + 1) :=
  Classical.epsilon (fun a => σ.Consecutive a b)

/-- The alternative directly below `b` (arbitrary when there is none). -/
noncomputable def dnN (σ : Order (Fin (n + 1))) (b : Fin (n + 1)) : Fin (n + 1) :=
  Classical.epsilon (fun c => σ.Consecutive b c)

theorem upN_spec {σ : Order (Fin (n + 1))} {b : Fin (n + 1)} (h : ∃ a, σ.Consecutive a b) :
    σ.Consecutive (upN σ b) b := Classical.epsilon_spec h

theorem dnN_spec {σ : Order (Fin (n + 1))} {b : Fin (n + 1)} (h : ∃ c, σ.Consecutive b c) :
    σ.Consecutive b (dnN σ b) := Classical.epsilon_spec h

theorem upN_eq {σ : Order (Fin (n + 1))} {a b : Fin (n + 1)} (h : σ.Consecutive a b) : upN σ b = a :=
  up_unique (upN_spec ⟨a, h⟩) h

theorem dnN_eq {σ : Order (Fin (n + 1))} {b c : Fin (n + 1)} (h : σ.Consecutive b c) : dnN σ b = c :=
  down_unique (dnN_spec ⟨c, h⟩) h

/-- Strictly between the two neighbours of `b` lies only `b`. -/
theorem between_neighbours {σ : Order (Fin (n + 1))} {a b c d : Fin (n + 1)} (hab : σ.Consecutive a b)
    (hbc : σ.Consecutive b c) (h1 : σ a d = true) (h2 : σ d c = true) : d = b := by
  by_contra hdb
  rcases σ.total hdb with h | h
  · exact hab.2.2 d ⟨h1, h⟩
  · exact hbc.2.2 d ⟨h, h2⟩

/-! ### Laws on a triple, through Codex's patterns -/

section Laws
variable {α : Type*}

/-- `D` satisfies the never-condition `p` for `x` on the triple `{x, y, z}`. -/
def NeverOn (D : Domain α) (x y z : α) (p : Fin 3) : Prop := ∀ r ∈ D, Never r x y z p

/-- The common law of a triple, in pattern form (Codex's finite characterisation). -/
theorem pattern_law {D : Domain α} (hD : IsCondorcet D) {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) :
    ∃ x p : Fin 3, ∀ r ∈ D, (orderPattern r a b c).Never x p := by
  classical
  obtain ⟨x, p, H⟩ := Pattern.finite_characterization _ (patternFamily_closed hD hab hbc)
  refine ⟨x, p, fun r hr => ?_⟩
  have hcode : (orderPattern r a b c).code ∈ patternFamily D a b c :=
    Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have ht := H _ hcode
  rwa [Pattern.decode_code _ (orderPattern_valid r hab hbc)] at ht

theorem never0_iff (r : Order α) (a b c : α) (p : Fin 3) :
    (orderPattern r a b c).Never 0 p ↔ Never r a b c p := by
  fin_cases p <;> simp [Pattern.Never, NeverBits, orderPattern, Never]

theorem never2_iff (r : Order α) {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) (p : Fin 3) :
    (orderPattern r a b c).Never 2 p ↔ Never r c a b p := by
  fin_cases p <;> simp [Pattern.Never, NeverBits, orderPattern, Never, r.reverse_comparison hac,
    r.reverse_comparison hbc]

theorem pattern_eq {r : Order α} {a b c : α} {u v w : Bool} (h1 : r a b = u) (h2 : r a c = v)
    (h3 : r b c = w) : orderPattern r a b c = (u, v, w) := by
  simp [orderPattern, h1, h2, h3]

end Laws

/-! ### The finite pattern facts (decided by evaluation) -/

/-- `σ, lift, drop` give `abc, bac, acb`: the law is "`a` never last" or "`c` never first". -/
theorem pull_patterns : ∀ x p : Fin 3, Pattern.Never (true, true, true) x p →
    Pattern.Never (false, true, true) x p → Pattern.Never (true, true, false) x p →
    (x = 0 ∧ p = 2) ∨ (x = 2 ∧ p = 0) := by decide

/-- Both upper, on `(b₁, b₂, q)`: the law is "`q` never first". -/
theorem upper_patterns : ∀ x p : Fin 3, Pattern.Never (false, true, true) x p →
    Pattern.Never (true, true, true) x p → Pattern.Never (false, false, true) x p →
    Pattern.Never (true, true, false) x p → x = 2 ∧ p = 0 := by decide

/-- Both lower, on `(b₁, b₂, p)`: the law is "`p` never last". -/
theorem lower_patterns : ∀ x p : Fin 3, Pattern.Never (true, false, false) x p →
    Pattern.Never (false, false, false) x p → Pattern.Never (true, true, false) x p →
    Pattern.Never (false, false, true) x p → x = 2 ∧ p = 2 := by decide

/-- Mixed, on `(b₁, b₂, q)` and on `(p, b₁, b₂)`: no pair of laws. -/
theorem mixed_patterns : ∀ u v : Bool, ∀ x p x' p' : Fin 3,
    Pattern.Never (true, true, false) x p → Pattern.Never (true, true, true) x p →
    Pattern.Never (false, false, true) x p → Pattern.Never (u, false, false) x p →
    Pattern.Never (v, true, true) x p →
    Pattern.Never (false, true, true) x' p' → Pattern.Never (true, true, true) x' p' →
    Pattern.Never (true, true, u) x' p' → Pattern.Never (false, false, v) x' p' →
    Pattern.Never (true, false, false) x' p' → False := by decide

/-! ### Free pairs -/

variable {D : Domain (Fin (n + 1))}

/-- `τ` is a lift of `b` in `σ`, inside `D`. -/
def IsLift (D : Domain (Fin (n + 1))) (σ τ : Order (Fin (n + 1))) (b : Fin (n + 1)) : Prop :=
  τ ∈ D ∧ deletedOrder b τ = deletedOrder b σ ∧ orderSlot b τ < orderSlot b σ

/-- `τ` is a drop of `b` in `σ`, inside `D`. -/
def IsDrop (D : Domain (Fin (n + 1))) (σ τ : Order (Fin (n + 1))) (b : Fin (n + 1)) : Prop :=
  τ ∈ D ∧ deletedOrder b τ = deletedOrder b σ ∧ orderSlot b σ < orderSlot b τ

/-- A free pair `(σ, b)` with the neighbours `a` (directly above) and `c` (directly below). -/
structure FreePair (D : Domain (Fin (n + 1))) (σ : Order (Fin (n + 1))) (b a c : Fin (n + 1)) :
    Prop where
  mem : σ ∈ D
  lift : ∃ τ, IsLift D σ τ b
  drop : ∃ τ, IsDrop D σ τ b
  up : σ.Consecutive a b
  down : σ.Consecutive b c

theorem freePair_of_free {σ : Order (Fin (n + 1))} {b : Fin (n + 1)} (hσ : σ ∈ D)
    (hf : Free D σ b) : FreePair D σ b (upN σ b) (dnN σ b) := by
  obtain ⟨hl, hd⟩ := hf
  refine ⟨hσ, ?_, ?_, upN_spec (exists_up_of_hasLift hl), dnN_spec (exists_down_of_hasDrop hd)⟩
  · obtain ⟨τ, hτ, h1, h2⟩ := hl; exact ⟨τ, hτ, h1, h2⟩
  · obtain ⟨τ, hτ, h1, h2⟩ := hd; exact ⟨τ, hτ, h1, h2⟩

theorem IsLift.agree {σ τ : Order (Fin (n + 1))} {b : Fin (n + 1)} (h : IsLift D σ τ b) :
    AgreeOff σ τ b := agreeOff_of_deleted h.2.1

theorem IsDrop.agree {σ τ : Order (Fin (n + 1))} {b : Fin (n + 1)} (h : IsDrop D σ τ b) :
    AgreeOff σ τ b := agreeOff_of_deleted h.2.1

namespace FreePair

variable {σ : Order (Fin (n + 1))} {b a c : Fin (n + 1)}

theorem ne_ab (h : FreePair D σ b a c) : a ≠ b := h.up.1
theorem ne_bc (h : FreePair D σ b a c) : b ≠ c := h.down.1
theorem sab (h : FreePair D σ b a c) : σ a b = true := h.up.2.1
theorem sbc (h : FreePair D σ b a c) : σ b c = true := h.down.2.1
theorem sac (h : FreePair D σ b a c) : σ a c = true := σ.trans h.sab h.sbc
theorem ne_ac (h : FreePair D σ b a c) : a ≠ c := by
  intro e; have := h.sac; rw [e, σ.irrefl] at this; contradiction

/-- Facts about a lift of `b`: it crosses `a`, and leaves `a` directly above `c`. -/
theorem lift_facts (h : FreePair D σ b a c) {τ : Order (Fin (n + 1))} (ht : IsLift D σ τ b) :
    τ a b = false ∧ τ b a = true ∧ τ a c = true ∧ τ b c = true ∧ τ.Consecutive a c := by
  obtain ⟨_, hdel, hslot⟩ := ht
  have hag := agreeOff_of_deleted hdel
  have hrk := rank_lt_of_slot_lt hslot
  have h1 : τ a b = false := lift_crosses_adjacent σ τ a b h.ne_ab hdel hslot h.sab h.up.2.2
  have h2 : τ b a = true := by rw [τ.reverse_comparison h.ne_ab, h1]; rfl
  have h3 : τ a c = true := by rw [← hag a c h.ne_ab h.ne_bc.symm]; exact h.sac
  have h4 : τ b c = true := lift_keeps_below hag hrk h.ne_bc.symm h.sbc
  refine ⟨h1, h2, h3, h4, h.ne_ac, h3, ?_⟩
  rintro d ⟨hd1, hd2⟩
  by_cases hdb : d = b
  · rw [hdb, h1] at hd1; contradiction
  · have e1 : σ a d = true := by rw [hag a d h.ne_ab hdb]; exact hd1
    have e2 : σ d c = true := by rw [hag d c hdb h.ne_bc.symm]; exact hd2
    exact hdb (between_neighbours h.up h.down e1 e2)

/-- Facts about a drop of `b`: it crosses `c`, and leaves `a` directly above `c`. -/
theorem drop_facts (h : FreePair D σ b a c) {τ : Order (Fin (n + 1))} (ht : IsDrop D σ τ b) :
    τ b c = false ∧ τ c b = true ∧ τ a c = true ∧ τ a b = true ∧ τ.Consecutive a c := by
  obtain ⟨_, hdel, hslot⟩ := ht
  have hag := agreeOff_of_deleted hdel
  have hrk := rank_lt_of_slot_lt hslot
  have h1 : τ b c = false := drop_crosses_adjacent σ τ b c h.ne_bc hdel hslot h.sbc h.down.2.2
  have h2 : τ c b = true := by rw [τ.reverse_comparison h.ne_bc, h1]; rfl
  have h3 : τ a c = true := by rw [← hag a c h.ne_ab h.ne_bc.symm]; exact h.sac
  have h4 : τ a b = true := drop_keeps_above hag hrk h.ne_ab h.sab
  refine ⟨h1, h2, h3, h4, h.ne_ac, h3, ?_⟩
  rintro d ⟨hd1, hd2⟩
  by_cases hdb : d = b
  · rw [hdb, h1] at hd2; contradiction
  · have e1 : σ a d = true := by rw [hag a d h.ne_ab hdb]; exact hd1
    have e2 : σ d c = true := by rw [hag d c hdb h.ne_bc.symm]; exact hd2
    exact hdb (between_neighbours h.up h.down e1 e2)

/-- **Lemma `lem:pull`, first part.** -/
theorem law (h : FreePair D σ b a c) (hD : IsCondorcet D) :
    NeverOn D a b c 2 ∨ NeverOn D c a b 0 := by
  obtain ⟨τ, ht⟩ := h.lift
  obtain ⟨ρ, hr⟩ := h.drop
  obtain ⟨τ1, -, τ3, τ4, -⟩ := h.lift_facts ht
  obtain ⟨ρ1, -, ρ3, ρ4, -⟩ := h.drop_facts hr
  obtain ⟨x, p, H⟩ := pattern_law hD h.ne_ab h.ne_bc
  have k1 := H σ h.mem
  rw [pattern_eq h.sab h.sac h.sbc] at k1
  have k2 := H τ ht.1
  rw [pattern_eq τ1 τ3 τ4] at k2
  have k3 := H ρ hr.1
  rw [pattern_eq ρ4 ρ3 ρ1] at k3
  rcases pull_patterns x p k1 k2 k3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; intro r hr'; exact (never0_iff r a b c 2).mp (H r hr')
  · right; intro r hr'; exact (never2_iff r h.ne_ac h.ne_bc 0).mp (H r hr')

/-- **Lemma `lem:pull`, last part**: a maximal domain does not satisfy both laws. -/
theorem not_both (h : FreePair D σ b a c) (hD : IsMaximal D) :
    ¬ (NeverOn D a b c 2 ∧ NeverOn D c a b 0) := by
  rintro ⟨h2, h0⟩
  have hfix : ∀ u ∈ D, u a c = true := by
    intro u hu
    have e2 := (CDCert.Supermult.never_two u a b c).mp (h2 u hu)
    have e0 := (CDCert.Supermult.never_zero u c a b).mp (h0 u hu)
    by_contra hac
    have hca : u c a = true := (u.total h.ne_ac).resolve_left hac
    have hab : u a b = true := e2.resolve_right hac
    have hcb : u c b = true := u.trans hca hab
    rcases e0 with e | e
    · rw [hca] at e; contradiction
    · rw [hcb] at e; contradiction
  obtain ⟨τ, ht⟩ := h.lift
  obtain ⟨-, -, -, -, hcon⟩ := h.lift_facts ht
  exact hD.fixed_pair_not_consecutive τ a c h.ne_ac ht.1 hfix hcon.2.2

/-- **The letter `(a, c)` of a lift is locked** when `a` is never last on `T`. -/
theorem lift_locked (h : FreePair D σ b a c) (hU : NeverOn D a b c 2) {τ : Order (Fin (n + 1))}
    (ht : IsLift D σ τ b) : ¬ HasLift D τ c ∧ ¬ HasDrop D τ a := by
  obtain ⟨-, τ2, τ3, -, hcon⟩ := h.lift_facts ht
  constructor
  · rintro ⟨μ, hμ, hdel, hslot⟩
    have hag := agreeOff_of_deleted hdel
    have m1 : μ a c = false := lift_crosses_adjacent τ μ a c h.ne_ac hdel hslot τ3 hcon.2.2
    have m2 : μ b a = true := by rw [← hag b a h.ne_bc h.ne_ac]; exact τ2
    have e := (CDCert.Supermult.never_two μ a b c).mp (hU μ hμ)
    rw [μ.asymmetric m2, m1] at e
    simp at e
  · rintro ⟨μ, hμ, hdel, hslot⟩
    have hag := agreeOff_of_deleted hdel
    have m1 : μ a c = false := drop_crosses_adjacent τ μ a c h.ne_ac hdel hslot τ3 hcon.2.2
    have m2 : μ b a = true := drop_keeps_above hag (rank_lt_of_slot_lt hslot) h.ne_ab.symm τ2
    have e := (CDCert.Supermult.never_two μ a b c).mp (hU μ hμ)
    rw [μ.asymmetric m2, m1] at e
    simp at e

/-- **The letter `(a, c)` of a drop is locked** when `c` is never first on `T`. -/
theorem drop_locked (h : FreePair D σ b a c) (hL : NeverOn D c a b 0) {τ : Order (Fin (n + 1))}
    (ht : IsDrop D σ τ b) : ¬ HasLift D τ c ∧ ¬ HasDrop D τ a := by
  obtain ⟨-, τ2, τ3, -, hcon⟩ := h.drop_facts ht
  constructor
  · rintro ⟨μ, hμ, hdel, hslot⟩
    have hag := agreeOff_of_deleted hdel
    have m1 : μ a c = false := lift_crosses_adjacent τ μ a c h.ne_ac hdel hslot τ3 hcon.2.2
    have m1' : μ c a = true := by rw [μ.reverse_comparison h.ne_ac, m1]; rfl
    have m2 : μ c b = true := lift_keeps_below hag (rank_lt_of_slot_lt hslot) h.ne_bc τ2
    have e := (CDCert.Supermult.never_zero μ c a b).mp (hL μ hμ)
    rw [m1', m2] at e
    simp at e
  · rintro ⟨μ, hμ, hdel, hslot⟩
    have hag := agreeOff_of_deleted hdel
    have m1 : μ a c = false := drop_crosses_adjacent τ μ a c h.ne_ac hdel hslot τ3 hcon.2.2
    have m1' : μ c a = true := by rw [μ.reverse_comparison h.ne_ac, m1]; rfl
    have m2 : μ c b = true := by rw [← hag c b h.ne_ac.symm h.ne_ab.symm]; exact τ2
    have e := (CDCert.Supermult.never_zero μ c a b).mp (hL μ hμ)
    rw [m1', m2] at e
    simp at e

/-- For an upper free pair, an order putting `c` first and `a` in the middle on `T`. -/
theorem chi_upper (h : FreePair D σ b a c) (hD : IsMaximal D) (hU : NeverOn D a b c 2) :
    ∃ χ ∈ D, χ c a = true ∧ χ c b = true ∧ χ a b = true := by
  have hn : ¬ NeverOn D c a b 0 := fun h0 => h.not_both hD ⟨hU, h0⟩
  unfold NeverOn at hn
  push_neg at hn
  obtain ⟨χ, hχ, hne⟩ := hn
  rw [CDCert.Supermult.never_zero] at hne
  push_neg at hne
  have hca : χ c a = true := by simpa using hne.1
  have hcb : χ c b = true := by simpa using hne.2
  have e := (CDCert.Supermult.never_two χ a b c).mp (hU χ hχ)
  have hac : χ a c = false := χ.asymmetric hca
  rw [hac] at e
  exact ⟨χ, hχ, hca, hcb, e.resolve_right (by simp)⟩

/-- For a lower free pair: `c` is never first on `T`, and an order putting `b` first and `a` last. -/
theorem chi_lower (h : FreePair D σ b a c) (hD : IsCondorcet D) (hL : ¬ NeverOn D a b c 2) :
    NeverOn D c a b 0 ∧ ∃ χ ∈ D, χ b a = true ∧ χ c a = true ∧ χ b c = true := by
  have h0 : NeverOn D c a b 0 := (h.law hD).resolve_left hL
  refine ⟨h0, ?_⟩
  unfold NeverOn at hL
  push_neg at hL
  obtain ⟨χ, hχ, hne⟩ := hL
  rw [CDCert.Supermult.never_two] at hne
  push_neg at hne
  have hab : χ a b = false := by simpa using hne.1
  have hac : χ a c = false := by simpa using hne.2
  have hba : χ b a = true := by rw [χ.reverse_comparison h.ne_ab, hab]; rfl
  have hca : χ c a = true := by rw [χ.reverse_comparison h.ne_ac, hac]; rfl
  have e := (CDCert.Supermult.never_zero χ c a b).mp (h0 χ hχ)
  rw [hca] at e
  have hcb : χ c b = false := e.resolve_left (by simp)
  have hbc : χ b c = true := by rw [χ.reverse_comparison h.ne_bc.symm, hcb]; rfl
  exact ⟨χ, hχ, hba, hca, hbc⟩

end FreePair

/-! ### The letter of a consecutive pair -/

theorem letter_of_consecutive {τ : Order (Fin (n + 1))} {a c : Fin (n + 1)} (hc : τ.Consecutive a c) :
    ∃ j : Fin n, j.val = τ.rank a ∧ τ.atPos j.castSucc = a ∧ τ.atPos j.succ = c := by
  have e := hc.rank_succ
  have hcl := τ.rank_lt_size c
  simp only [Fintype.card_fin] at hcl
  refine ⟨⟨τ.rank a, by omega⟩, rfl, ?_, ?_⟩
  · exact τ.rank_injective (by rw [Order.rank_atPos]; rfl)
  · exact τ.rank_injective (by rw [Order.rank_atPos, e]; rfl)

/-! ### The map `ψ` -/

/-- The order of `ψ(σ, b)`: a lift of `b` if `D` satisfies "`a` never last" on `T`, else a drop. -/
noncomputable def psiOrder (D : Domain (Fin (n + 1))) (σ : Order (Fin (n + 1))) (b : Fin (n + 1)) :
    Order (Fin (n + 1)) :=
  Classical.epsilon (fun τ => (NeverOn D (upN σ b) b (dnN σ b) 2 → IsLift D σ τ b) ∧
    (¬ NeverOn D (upN σ b) b (dnN σ b) 2 → IsDrop D σ τ b))

theorem psiOrder_spec {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : FreePair D σ b (upN σ b) (dnN σ b)) :
    (NeverOn D (upN σ b) b (dnN σ b) 2 → IsLift D σ (psiOrder D σ b) b) ∧
      (¬ NeverOn D (upN σ b) b (dnN σ b) 2 → IsDrop D σ (psiOrder D σ b) b) := by
  apply Classical.epsilon_spec (p := fun τ => (NeverOn D (upN σ b) b (dnN σ b) 2 → IsLift D σ τ b) ∧
    (¬ NeverOn D (upN σ b) b (dnN σ b) 2 → IsDrop D σ τ b))
  by_cases hU : NeverOn D (upN σ b) b (dnN σ b) 2
  · obtain ⟨τ, ht⟩ := h.lift
    exact ⟨τ, fun _ => ht, fun hn => absurd hU hn⟩
  · obtain ⟨τ, ht⟩ := h.drop
    exact ⟨τ, fun hu => absurd hu hU, fun _ => ht⟩

/-- `ψ(b, σ) = (τ, position of a in τ)`. -/
noncomputable def psi (D : Domain (Fin (n + 1))) (v : Fin (n + 1) × Order (Fin (n + 1))) :
    Order (Fin (n + 1)) × Nat :=
  (psiOrder D v.2 v.1, (psiOrder D v.2 v.1).rank (upN v.2 v.1))

theorem psi_consecutive (_hD : IsCondorcet D) {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : FreePair D σ b (upN σ b) (dnN σ b)) :
    psiOrder D σ b ∈ D ∧ (psiOrder D σ b).Consecutive (upN σ b) (dnN σ b) := by
  have sp := psiOrder_spec h
  by_cases hU : NeverOn D (upN σ b) b (dnN σ b) 2
  · exact ⟨(sp.1 hU).1, (h.lift_facts (sp.1 hU)).2.2.2.2⟩
  · exact ⟨(sp.2 hU).1, (h.drop_facts (sp.2 hU)).2.2.2.2⟩

/-- **The image of a free pair is a locked letter.** -/
theorem psi_locked (hD : IsMaximal D) {σ : Order (Fin (n + 1))} {b : Fin (n + 1)}
    (h : FreePair D σ b (upN σ b) (dnN σ b)) :
    ∃ j : Fin n, j.val = (psiOrder D σ b).rank (upN σ b) ∧ Locked D (psiOrder D σ b) j := by
  obtain ⟨-, hcons⟩ := psi_consecutive hD.1 h
  obtain ⟨j, hj, hpa, hpc⟩ := letter_of_consecutive hcons
  refine ⟨j, hj, ?_⟩
  unfold Locked
  rw [hpa, hpc]
  have sp := psiOrder_spec h
  by_cases hU : NeverOn D (upN σ b) b (dnN σ b) 2
  · exact h.lift_locked hU (sp.1 hU)
  · exact h.drop_locked ((h.law hD.1).resolve_left hU) (sp.2 hU)

/-! ### Injectivity -/

/-- Two orders with the same deletion of `b` and the same upper neighbour of `b` are equal. -/
theorem eq_of_same_insertion {σ₁ σ₂ : Order (Fin (n + 1))} {b p : Fin (n + 1)}
    (hd : deletedOrder b σ₁ = deletedOrder b σ₂)
    (c₁ : σ₁.Consecutive p b) (c₂ : σ₂.Consecutive p b) : σ₁ = σ₂ := by
  classical
  apply deletedOrder_slot_injective b hd
  apply Fin.ext
  rw [orderSlot_val_eq_rank, orderSlot_val_eq_rank, c₁.rank_succ, c₂.rank_succ]
  have hag : AgreeOff σ₂ σ₁ b := agreeOff_of_deleted hd
  have e : σ₁.above p = σ₂.above p := by
    ext y
    simp only [Order.mem_above]
    by_cases hy : y = b
    · rw [hy, σ₁.asymmetric c₁.2.1, σ₂.asymmetric c₂.2.1]
    · rw [hag y p hy c₁.1]
  unfold Order.rank
  rw [e]

section Cases
variable {σ₁ σ₂ τ : Order (Fin (n + 1))} {b₁ b₂ p q : Fin (n + 1)}

/-- **Both upper.** -/
theorem both_upper (hD : IsMaximal D) (h₁ : FreePair D σ₁ b₁ p q) (h₂ : FreePair D σ₂ b₂ p q)
    (hb : b₁ ≠ b₂) (U₁ : NeverOn D p b₁ q 2) (U₂ : NeverOn D p b₂ q 2)
    (l₁ : IsLift D σ₁ τ b₁) (l₂ : IsLift D σ₂ τ b₂) : False := by
  obtain ⟨-, t1, -, -, tc⟩ := h₁.lift_facts l₁
  obtain ⟨-, t2, -, -, -⟩ := h₂.lift_facts l₂
  have tpq : τ p q = true := tc.2.1
  have ag₁ := l₁.agree
  have ag₂ := l₂.agree
  have s1a : σ₁ b₂ p = true := by rw [ag₁ b₂ p hb.symm h₁.ne_ab]; exact t2
  have s1b : σ₁ b₂ b₁ = true := σ₁.trans s1a h₁.sab
  have s1c : σ₁ b₂ q = true := by rw [ag₁ b₂ q hb.symm h₁.ne_bc.symm]; exact τ.trans t2 tpq
  have s2a : σ₂ b₁ p = true := by rw [ag₂ b₁ p hb h₂.ne_ab]; exact t1
  have s2b : σ₂ b₁ b₂ = true := σ₂.trans s2a h₂.sab
  have s2c : σ₂ b₁ q = true := by rw [ag₂ b₁ q hb h₂.ne_bc.symm]; exact τ.trans t1 tpq
  obtain ⟨ρ₁, d₁⟩ := h₁.drop
  obtain ⟨-, r1, -, -, -⟩ := h₁.drop_facts d₁
  have r1b : ρ₁ b₂ q = true := by rw [← d₁.agree b₂ q hb.symm h₁.ne_bc.symm]; exact s1c
  have r1c : ρ₁ b₂ b₁ = true := ρ₁.trans r1b r1
  obtain ⟨ρ₂, d₂⟩ := h₂.drop
  obtain ⟨-, r2, -, -, -⟩ := h₂.drop_facts d₂
  have r2b : ρ₂ b₁ q = true := by rw [← d₂.agree b₁ q hb h₂.ne_bc.symm]; exact s2c
  have r2c : ρ₂ b₁ b₂ = true := ρ₂.trans r2b r2
  obtain ⟨x, k, H⟩ := pattern_law hD.1 hb h₂.ne_bc
  have k1 := H σ₁ h₁.mem
  rw [pattern_eq (σ₁.asymmetric s1b) h₁.sbc s1c] at k1
  have k2 := H σ₂ h₂.mem
  rw [pattern_eq s2b s2c h₂.sbc] at k2
  have k3 := H ρ₁ d₁.1
  rw [pattern_eq (ρ₁.asymmetric r1c) (ρ₁.asymmetric r1) r1b] at k3
  have k4 := H ρ₂ d₂.1
  rw [pattern_eq r2c r2b (ρ₂.asymmetric r2)] at k4
  obtain ⟨rfl, rfl⟩ := upper_patterns x k k1 k2 k3 k4
  obtain ⟨χ, hχ, c1, c2, -⟩ := h₁.chi_upper hD U₁
  have e := (never2_iff χ h₁.ne_bc h₂.ne_bc 0).mp (H χ hχ)
  rw [CDCert.Supermult.never_zero, c2] at e
  have hqb₂ : χ q b₂ = false := e.resolve_left (by simp)
  have hb₂q : χ b₂ q = true := by rw [χ.reverse_comparison h₂.ne_bc.symm, hqb₂]; rfl
  have hb₂p : χ b₂ p = true := χ.trans hb₂q c1
  have e2 := (CDCert.Supermult.never_two χ p b₂ q).mp (U₂ χ hχ)
  rw [χ.asymmetric hb₂p, χ.asymmetric c1] at e2
  simp at e2

/-- **Both lower** (the mirror image). -/
theorem both_lower (hD : IsMaximal D) (h₁ : FreePair D σ₁ b₁ p q) (h₂ : FreePair D σ₂ b₂ p q)
    (hb : b₁ ≠ b₂) (L₁ : ¬ NeverOn D p b₁ q 2) (L₂ : ¬ NeverOn D p b₂ q 2)
    (d₁ : IsDrop D σ₁ τ b₁) (d₂ : IsDrop D σ₂ τ b₂) : False := by
  obtain ⟨-, t1, -, -, tc⟩ := h₁.drop_facts d₁
  obtain ⟨-, t2, -, -, -⟩ := h₂.drop_facts d₂
  have tpq : τ p q = true := tc.2.1
  have ag₁ := d₁.agree
  have ag₂ := d₂.agree
  have s1a : σ₁ q b₂ = true := by rw [ag₁ q b₂ h₁.ne_bc.symm hb.symm]; exact t2
  have s1b : σ₁ b₁ b₂ = true := σ₁.trans h₁.sbc s1a
  have s1c : σ₁ p b₂ = true := by rw [ag₁ p b₂ h₁.ne_ab hb.symm]; exact τ.trans tpq t2
  have s2a : σ₂ q b₁ = true := by rw [ag₂ q b₁ h₂.ne_bc.symm hb]; exact t1
  have s2b : σ₂ b₂ b₁ = true := σ₂.trans h₂.sbc s2a
  have s2c : σ₂ p b₁ = true := by rw [ag₂ p b₁ h₂.ne_ab hb]; exact τ.trans tpq t1
  obtain ⟨μ₁, l₁⟩ := h₁.lift
  obtain ⟨-, m1, -, -, -⟩ := h₁.lift_facts l₁
  have m1b : μ₁ p b₂ = true := by rw [← l₁.agree p b₂ h₁.ne_ab hb.symm]; exact s1c
  have m1c : μ₁ b₁ b₂ = true := μ₁.trans m1 m1b
  obtain ⟨μ₂, l₂⟩ := h₂.lift
  obtain ⟨-, m2, -, -, -⟩ := h₂.lift_facts l₂
  have m2b : μ₂ p b₁ = true := by rw [← l₂.agree p b₁ h₂.ne_ab hb]; exact s2c
  have m2c : μ₂ b₂ b₁ = true := μ₂.trans m2 m2b
  obtain ⟨x, k, H⟩ := pattern_law hD.1 hb h₂.ne_ab.symm
  have k1 := H σ₁ h₁.mem
  rw [pattern_eq s1b (σ₁.asymmetric h₁.sab) (σ₁.asymmetric s1c)] at k1
  have k2 := H σ₂ h₂.mem
  rw [pattern_eq (σ₂.asymmetric s2b) (σ₂.asymmetric s2c) (σ₂.asymmetric h₂.sab)] at k2
  have k3 := H μ₁ l₁.1
  rw [pattern_eq m1c m1 (μ₁.asymmetric m1b)] at k3
  have k4 := H μ₂ l₂.1
  rw [pattern_eq (μ₂.asymmetric m2c) (μ₂.asymmetric m2b) m2] at k4
  obtain ⟨rfl, rfl⟩ := lower_patterns x k k1 k2 k3 k4
  obtain ⟨-, χ, hχ, c1, c2, -⟩ := h₁.chi_lower hD.1 L₁
  have e := (never2_iff χ h₁.ne_ab.symm h₂.ne_ab.symm 2).mp (H χ hχ)
  rw [CDCert.Supermult.never_two, χ.asymmetric c1] at e
  have hpb₂ : χ p b₂ = true := e.resolve_left (by simp)
  have hqb₂ : χ q b₂ = true := χ.trans c2 hpb₂
  have e2 := (CDCert.Supermult.never_zero χ q p b₂).mp ((h₂.chi_lower hD.1 L₂).1 χ hχ)
  rw [c2, hqb₂] at e2
  simp at e2

/-- **Mixed**: `b₁` upper, `b₂` lower. -/
theorem mixed (hD : IsMaximal D) (h₁ : FreePair D σ₁ b₁ p q) (h₂ : FreePair D σ₂ b₂ p q)
    (hb : b₁ ≠ b₂) (U₁ : NeverOn D p b₁ q 2) (L₂ : ¬ NeverOn D p b₂ q 2)
    (l₁ : IsLift D σ₁ τ b₁) (d₂ : IsDrop D σ₂ τ b₂) : False := by
  obtain ⟨-, t1, -, -, tc⟩ := h₁.lift_facts l₁
  obtain ⟨-, t2, -, -, -⟩ := h₂.drop_facts d₂
  have tpq : τ p q = true := tc.2.1
  have ag₁ := l₁.agree
  have ag₂ := d₂.agree
  have tb₁q : τ b₁ q = true := τ.trans t1 tpq
  have tpb₂ : τ p b₂ = true := τ.trans tpq t2
  have tb₁b₂ : τ b₁ b₂ = true := τ.trans t1 tpb₂
  have s1q : σ₁ q b₂ = true := by rw [ag₁ q b₂ h₁.ne_bc.symm hb.symm]; exact t2
  have s1b : σ₁ b₁ b₂ = true := σ₁.trans h₁.sbc s1q
  have s1p : σ₁ p b₂ = true := σ₁.trans h₁.sab s1b
  have s2p : σ₂ b₁ p = true := by rw [ag₂ b₁ p hb h₂.ne_ab]; exact t1
  have s2b : σ₂ b₁ b₂ = true := σ₂.trans s2p h₂.sab
  have s2q : σ₂ b₁ q = true := σ₂.trans s2b h₂.sbc
  obtain ⟨χ, hχ, c1, c2, c3⟩ := h₁.chi_upper hD U₁
  have e := (CDCert.Supermult.never_zero χ q p b₂).mp ((h₂.chi_lower hD.1 L₂).1 χ hχ)
  rw [c1] at e
  have hqb₂ : χ q b₂ = false := e.resolve_left (by simp)
  have hb₂q : χ b₂ q = true := by rw [χ.reverse_comparison h₂.ne_bc.symm, hqb₂]; rfl
  have hb₂p : χ b₂ p = true := χ.trans hb₂q c1
  have hb₂b₁ : χ b₂ b₁ = true := χ.trans hb₂q c2
  obtain ⟨ρ, dr⟩ := h₁.drop
  obtain ⟨-, r1, -, r3, -⟩ := h₁.drop_facts dr
  have rq : ρ q b₂ = true := by rw [← dr.agree q b₂ h₁.ne_bc.symm hb.symm]; exact s1q
  have rp : ρ p b₂ = true := by rw [← dr.agree p b₂ h₁.ne_ab hb.symm]; exact s1p
  obtain ⟨μ, lm⟩ := h₂.lift
  obtain ⟨-, m1, -, m3, -⟩ := h₂.lift_facts lm
  have mp : μ b₁ p = true := by rw [← lm.agree b₁ p hb h₂.ne_ab]; exact s2p
  have mq : μ b₁ q = true := by rw [← lm.agree b₁ q hb h₂.ne_bc.symm]; exact s2q
  obtain ⟨x, k, H1⟩ := pattern_law hD.1 hb h₂.ne_bc
  obtain ⟨x', k', H2⟩ := pattern_law hD.1 h₁.ne_ab hb
  have a1 := H1 τ l₁.1
  rw [pattern_eq tb₁b₂ tb₁q (τ.asymmetric t2)] at a1
  have a2 := H1 σ₂ h₂.mem
  rw [pattern_eq s2b s2q h₂.sbc] at a2
  have a3 := H1 χ hχ
  rw [pattern_eq (χ.asymmetric hb₂b₁) (χ.asymmetric c2) hb₂q] at a3
  have a4 := H1 ρ dr.1
  rw [pattern_eq rfl (ρ.asymmetric r1) (ρ.asymmetric rq)] at a4
  have a5 := H1 μ lm.1
  rw [pattern_eq rfl mq m3] at a5
  have b1 := H2 τ l₁.1
  rw [pattern_eq (τ.asymmetric t1) tpb₂ tb₁b₂] at b1
  have b2 := H2 σ₁ h₁.mem
  rw [pattern_eq h₁.sab s1p s1b] at b2
  have b3 := H2 ρ dr.1
  rw [pattern_eq r3 rp rfl] at b3
  have b4 := H2 μ lm.1
  rw [pattern_eq (μ.asymmetric mp) (μ.asymmetric m1) rfl] at b4
  have b5 := H2 χ hχ
  rw [pattern_eq c3 (χ.asymmetric hb₂p) (χ.asymmetric hb₂b₁)] at b5
  exact mixed_patterns (ρ b₁ b₂) (μ b₁ b₂) x k x' k' a1 a2 a3 a4 a5 b1 b2 b3 b4 b5

/-- **Proposition `prop:free`, injectivity**, for preimages with common neighbours `p`, `q`. -/
theorem inj_core (hD : IsMaximal D) (h₁ : FreePair D σ₁ b₁ p q) (h₂ : FreePair D σ₂ b₂ p q)
    (s₁ : (NeverOn D p b₁ q 2 → IsLift D σ₁ τ b₁) ∧ (¬ NeverOn D p b₁ q 2 → IsDrop D σ₁ τ b₁))
    (s₂ : (NeverOn D p b₂ q 2 → IsLift D σ₂ τ b₂) ∧ (¬ NeverOn D p b₂ q 2 → IsDrop D σ₂ τ b₂)) :
    b₁ = b₂ ∧ σ₁ = σ₂ := by
  by_cases hb : b₁ = b₂
  · subst hb
    refine ⟨rfl, ?_⟩
    have hd₁ : deletedOrder b₁ τ = deletedOrder b₁ σ₁ := by
      by_cases U : NeverOn D p b₁ q 2
      · exact (s₁.1 U).2.1
      · exact (s₁.2 U).2.1
    have hd₂ : deletedOrder b₁ τ = deletedOrder b₁ σ₂ := by
      by_cases U : NeverOn D p b₁ q 2
      · exact (s₂.1 U).2.1
      · exact (s₂.2 U).2.1
    exact eq_of_same_insertion (hd₁.symm.trans hd₂) h₁.up h₂.up
  · exfalso
    by_cases U₁ : NeverOn D p b₁ q 2 <;> by_cases U₂ : NeverOn D p b₂ q 2
    · exact both_upper hD h₁ h₂ hb U₁ U₂ (s₁.1 U₁) (s₂.1 U₂)
    · exact mixed hD h₁ h₂ hb U₁ U₂ (s₁.1 U₁) (s₂.2 U₂)
    · exact mixed hD h₂ h₁ (Ne.symm hb) U₂ U₁ (s₂.1 U₂) (s₁.2 U₁)
    · exact both_lower hD h₁ h₂ hb U₁ U₂ (s₁.2 U₁) (s₂.2 U₂)

end Cases

theorem psi_inj (hD : IsMaximal D) {σ₁ σ₂ : Order (Fin (n + 1))} {b₁ b₂ : Fin (n + 1)}
    (h₁ : FreePair D σ₁ b₁ (upN σ₁ b₁) (dnN σ₁ b₁)) (h₂ : FreePair D σ₂ b₂ (upN σ₂ b₂) (dnN σ₂ b₂))
    (heq : psi D (b₁, σ₁) = psi D (b₂, σ₂)) : b₁ = b₂ ∧ σ₁ = σ₂ := by
  simp only [psi, Prod.mk.injEq] at heq
  obtain ⟨hτ, hj⟩ := heq
  have sp₁ := psiOrder_spec h₁
  have sp₂ := psiOrder_spec h₂
  obtain ⟨-, hc₁⟩ := psi_consecutive hD.1 h₁
  obtain ⟨-, hc₂⟩ := psi_consecutive hD.1 h₂
  rw [← hτ] at sp₂ hj hc₂
  have ha : upN σ₁ b₁ = upN σ₂ b₂ := (psiOrder D σ₁ b₁).rank_injective hj
  rw [← ha] at hc₂ h₂ sp₂
  have hc : dnN σ₁ b₁ = dnN σ₂ b₂ := down_unique hc₁ hc₂
  rw [← hc] at h₂ sp₂
  exact inj_core hD h₁ h₂ sp₁ sp₂

/-! ### Counting -/

/-- The free pairs `(b, σ)`. -/
noncomputable def freePairs (D : Domain (Fin (n + 1))) : Finset (Fin (n + 1) × Order (Fin (n + 1))) := by
  classical
  exact (Finset.univ ×ˢ D).filter (fun v => Free D v.2 v.1)

/-- The locked letters `(τ, j)`, with `j` as a natural number. -/
noncomputable def lockedLetters (D : Domain (Fin (n + 1))) : Finset (Order (Fin (n + 1)) × Nat) := by
  classical
  exact ((D ×ˢ (Finset.univ : Finset (Fin n))).filter (fun v => Locked D v.1 v.2)).image
    (fun v => (v.1, v.2.val))

theorem card_freePairs : (freePairs D).card = freeCount D := by
  classical
  unfold freePairs freeCount freeOrders
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

theorem card_lockedLetters : (lockedLetters D).card = lockedCount D := by
  classical
  unfold lockedLetters lockedCount
  rw [Finset.card_image_of_injective _ (by
    rintro ⟨τ, j⟩ ⟨τ', j'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, Fin.ext h.2⟩)]
  rw [Finset.card_filter, Finset.sum_product]

/-- **Proposition `prop:free`**: in a maximal Condorcet domain the free pairs inject into the
locked letters. -/
theorem free_le_locked (hD : IsMaximal D) : freeCount D ≤ lockedCount D := by
  classical
  rw [← card_freePairs, ← card_lockedLetters]
  apply Finset.card_le_card_of_injOn (psi D)
  · intro v hv
    rw [Finset.mem_coe] at hv
    unfold freePairs at hv
    have hv' := Finset.mem_filter.mp hv
    have hσ : v.2 ∈ D := (Finset.mem_product.mp hv'.1).2
    have h := freePair_of_free hσ hv'.2
    obtain ⟨hmem, -⟩ := psi_consecutive hD.1 h
    obtain ⟨j, hj, hl⟩ := psi_locked hD h
    rw [Finset.mem_coe]
    unfold lockedLetters
    rw [Finset.mem_image]
    refine ⟨(psiOrder D v.2 v.1, j),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem, Finset.mem_univ _⟩, hl⟩, ?_⟩
    simp only [psi, hj]
  · intro v₁ hv₁ v₂ hv₂ heq
    rw [Finset.mem_coe] at hv₁ hv₂
    unfold freePairs at hv₁ hv₂
    have h1 := Finset.mem_filter.mp hv₁
    have h2 := Finset.mem_filter.mp hv₂
    obtain ⟨b₁, σ₁⟩ := v₁
    obtain ⟨b₂, σ₂⟩ := v₂
    obtain ⟨e1, e2⟩ := psi_inj hD (freePair_of_free (Finset.mem_product.mp h1.1).2 h1.2)
      (freePair_of_free (Finset.mem_product.mp h2.1).2 h2.2) heq
    exact Prod.ext e1 e2

end CDCert.FreeLocked
