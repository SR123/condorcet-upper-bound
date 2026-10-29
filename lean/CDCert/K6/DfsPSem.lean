/-
CDCert.K6.DfsPSem — soundness of the pruned depth-first check `dfsP` of `CDCert.K6.Defs7`.

* `testBit_stepEnc_high`, `testBit_runE_high`: above bit 64 an encoded step is a bitwise AND;
* `testBit_forcedAll`: the forced mask of a list of groups is the AND of all their options;
* **`dfsP_sound`**: if `dfsP leafOK (wp gs full bad) e = true` then for every choice `c` of
  one option per group, a nonzero final state without any order of `bad` (inside `full`)
  satisfies `leafOK`. A pruned branch contains an order of `bad` that every later option
  keeps, so it cannot end in such a state.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs7
import CDCert.K6.Sound

namespace CDCert.K6

open CDCert

set_option autoImplicit false

theorem testBit_stepEnc_high (e o i : Nat) (hi : 64 ≤ i) :
    (stepEnc e o).testBit i = (e.testBit i && o.testBit i) := by
  rw [stepEnc_eq, Nat.testBit_or, Nat.testBit_and, testBit_small (mod_hashP_lt _) hi, Bool.or_false]

theorem testBit_runE_high : ∀ (c : List Nat) (e i : Nat), 64 ≤ i →
    (runE e c).testBit i = (e.testBit i && c.all (fun o => o.testBit i))
  | [], e, i, _ => by simp [runE]
  | o :: c, e, i, hi => by
    show (runE (stepEnc e o) c).testBit i = _
    rw [testBit_runE_high c _ i hi, testBit_stepEnc_high e o i hi, List.all_cons, Bool.and_assoc]

theorem testBit_allAnd (i : Nat) : ∀ (g : List Nat) (acc : Nat),
    (allAnd g acc).testBit i = (acc.testBit i && g.all (fun o => o.testBit i))
  | [], acc => by simp [allAnd]
  | o :: g, acc => by
    show (Nat.land o (allAnd g acc)).testBit i = _
    rw [land_eq', Nat.testBit_and, testBit_allAnd i g acc, List.all_cons]
    cases o.testBit i <;> cases acc.testBit i <;> simp

theorem testBit_forcedAll (i : Nat) (full : Nat) : ∀ (gs : List (List Nat)),
    (forcedAll gs full).testBit i = (full.testBit i && gs.all (fun g => g.all (fun o => o.testBit i)))
  | [] => by simp [forcedAll]
  | g :: gs => by
    show (allAnd g (forcedAll gs full)).testBit i = _
    rw [testBit_allAnd, testBit_forcedAll i full gs, List.all_cons]
    cases full.testBit i <;> cases g.all (fun o => o.testBit i) <;> simp

theorem wp_cons (g : List Nat) (rest : List (List Nat)) (full bad : Nat) :
    wp (g :: rest) full bad = (g, Nat.land (forcedAll rest full) bad) :: wp rest full bad := rfl

theorem choice_all_testBit {i : Nat} : ∀ {c : List Nat} {gs : List (List Nat)}, IsChoice c gs →
    gs.all (fun g => g.all (fun o => o.testBit i)) = true → c.all (fun o => o.testBit i) = true
  | [], [], _, _ => rfl
  | o :: c, g :: gs, hc, h => by
    obtain ⟨o', ho', c', hc', he⟩ := isChoice_cons_iff.mp hc
    cases he
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp h.1 o ho', choice_all_testBit hc' h.2⟩
  | [], _ :: _, hc, _ => by
    obtain ⟨_, _, _, _, he⟩ := isChoice_cons_iff.mp hc
    cases he
  | _ :: _, [], hc, _ => by
    rw [isChoice_nil_iff] at hc
    cases hc

/-- **Soundness of the pruned depth-first check.** -/
theorem dfsP_sound (leafOK : Nat → Bool) (full bad : Nat) (hbad : ∀ i, i < 64 → bad.testBit i = false) :
    ∀ (gs : List (List Nat)) (e : Nat), dfsP leafOK (wp gs full bad) e = true →
      ∀ c, IsChoice c gs → runE e c ≠ 0 →
        (∀ i, bad.testBit i = true → full.testBit i = true → (runE e c).testBit i = false) →
        leafOK (runE e c) = true
  | [], e, h, c, hc, _, _ => by
    rw [isChoice_nil_iff] at hc
    subst hc
    exact h
  | g :: rest, e, h, c, hc, hne, hex => by
    obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
    rw [wp_cons] at h
    have hstep := (optLoop_eq_true
      (fun o => Nat.rec (motive := fun _ => Bool) true
        (fun e' _ => Bool.rec (motive := fun _ => Bool) true (dfsP leafOK (wp rest full bad) (Nat.succ e'))
          (Nat.beq (Nat.land (Nat.succ e') (Nat.land (forcedAll rest full) bad)) 0)) (stepEnc e o)) g).mp h o ho
    show leafOK (runE (stepEnc e o) c') = true
    have hne' : runE (stepEnc e o) c' ≠ 0 := hne
    have hex' : ∀ i, bad.testBit i = true → full.testBit i = true → (runE (stepEnc e o) c').testBit i = false := hex
    cases hs : stepEnc e o with
    | zero =>
      rw [hs, runE_zero] at hne'
      exact absurd rfl hne'
    | succ e' =>
      rw [hs] at hstep hne' hex'
      simp only at hstep
      cases hb : Nat.beq (Nat.land (Nat.succ e') (Nat.land (forcedAll rest full) bad)) 0
      · -- the prune fired: impossible
        exfalso
        obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.ne_of_beq_eq_false hb)
        rw [land_eq', Nat.testBit_and, land_eq', Nat.testBit_and, testBit_forcedAll] at hi
        simp only [Bool.and_eq_true] at hi
        obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hi
        have hi64 : 64 ≤ i := by
          apply Classical.byContradiction
          intro hlt
          rw [hbad i (by omega)] at h4
          cases h4
        have := hex' i h4 h2
        rw [testBit_runE_high c' _ i hi64, h1, choice_all_testBit hc' h3] at this
        cases this
      · rw [hb] at hstep
        exact dfsP_sound leafOK full bad hbad rest (Nat.succ e') hstep c' hc' hne' hex'

end CDCert.K6
