/-
CDCert.Check — an abstract depth-first checker and its soundness theorem.

The case generator for the finite lemma is a search over choices (one option
per constraint group) with pruning. For a kernel proof we do not need the list
of all cases, only the fact that every surviving case passes a test. This file
gives that "check-all" form for an arbitrary state type `σ` and option type `ω`
acting on states:

* `runChoice act s c` applies the options of `c` to the state `s`, in order;
* `dfsCheck act prune leafOK gs s` is the Boolean the kernel evaluates;
* `dfsCheck_sound`: if the check returns `true` and `prune` is sound for a goal,
  then every choice whose final state meets the goal passes `leafOK`;
* `dfsCheck_noPrune_iff`: without pruning the check is exact;
* `dfsCheck_append_of_forall`: the top levels can be split into separately
  checked subtrees (parallel kernel checks);
* `runChoice_sim`: a state encoding that commutes with the action transfers
  results between representations (used for Nat bitsets).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Enum

namespace CDCert

section Abstract
variable {σ ω : Type}

/-- Apply the options of a choice to a state, in order. -/
def runChoice (act : ω → σ → σ) : σ → List ω → σ
  | s, [] => s
  | s, o :: os => runChoice act (act o s) os

/-- The depth-first checker. At a node with remaining groups `g :: gs` either
the prune test fires, or every option of `g` leads to a passing subtree. At a
leaf the test `leafOK` is evaluated. -/
def dfsCheck (act : ω → σ → σ) (prune : List (List ω) → σ → Bool) (leafOK : σ → Bool) :
    List (List ω) → σ → Bool
  | [], s => leafOK s
  | g :: gs, s =>
      prune (g :: gs) s || g.all (fun o => dfsCheck act prune leafOK gs (act o s))

/-- A prune test is sound for `goal` if, whenever it fires, no completion of the
state meets the goal. -/
def PruneSoundFor (act : ω → σ → σ) (prune : List (List ω) → σ → Bool) (goal : σ → Bool) :
    Prop :=
  ∀ (gs : List (List ω)) (s : σ), prune gs s = true →
    ∀ c, IsChoice c gs → goal (runChoice act s c) = false

/-- **Soundness of the checker.** -/
theorem dfsCheck_sound {act : ω → σ → σ} {prune : List (List ω) → σ → Bool}
    {leafOK goal : σ → Bool} (hp : PruneSoundFor act prune goal) :
    ∀ (gs : List (List ω)) (s : σ), dfsCheck act prune leafOK gs s = true →
      ∀ c, IsChoice c gs → goal (runChoice act s c) = true →
        leafOK (runChoice act s c) = true := by
  intro gs
  induction gs with
  | nil =>
    intro s h c hc _
    rw [isChoice_nil_iff] at hc
    subst hc
    exact h
  | cons g gs ih =>
    intro s h c hc hg
    simp only [dfsCheck, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with hpr | hall
    · rw [hp (g :: gs) s hpr c hc] at hg
      cases hg
    · obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      exact ih (act o s) (hall o ho) c' hc' hg

/-- Without pruning, the check is exactly "every choice passes". -/
theorem dfsCheck_noPrune_iff {act : ω → σ → σ} {leafOK : σ → Bool} :
    ∀ (gs : List (List ω)) (s : σ),
      dfsCheck act (fun _ _ => false) leafOK gs s = true ↔
        ∀ c, IsChoice c gs → leafOK (runChoice act s c) = true := by
  intro gs
  induction gs with
  | nil =>
    intro s
    simp only [dfsCheck, isChoice_nil_iff]
    constructor
    · rintro h c rfl
      exact h
    · intro h
      exact h [] rfl
  | cons g gs ih =>
    intro s
    simp only [dfsCheck, Bool.false_or, List.all_eq_true]
    constructor
    · intro h c hc
      obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      exact (ih (act o s)).mp (h o ho) c' hc'
    · intro h o ho
      exact (ih (act o s)).mpr (fun c' hc' => h (o :: c') (IsChoice.cons ho hc'))

/-- **Splitting.** To check groups `gs₁ ++ gs₂` it suffices to check the
subtree below every choice for `gs₁` (pruning on the `gs₁` levels is simply not
used). This lets the top of the search be split across independent kernel
checks. -/
theorem dfsCheck_append_of_forall {act : ω → σ → σ} {prune : List (List ω) → σ → Bool}
    {leafOK : σ → Bool} (gs₂ : List (List ω)) :
    ∀ (gs₁ : List (List ω)) (s : σ),
      (∀ p, IsChoice p gs₁ → dfsCheck act prune leafOK gs₂ (runChoice act s p) = true) →
        dfsCheck act prune leafOK (gs₁ ++ gs₂) s = true := by
  intro gs₁
  induction gs₁ with
  | nil =>
    intro s h
    exact h [] IsChoice.nil
  | cons g gs₁ ih =>
    intro s h
    simp only [List.cons_append, dfsCheck, Bool.or_eq_true, List.all_eq_true]
    refine Or.inr (fun o ho => ih (act o s) (fun p hp => ?_))
    exact h (o :: p) (IsChoice.cons ho hp)

theorem runChoice_append (act : ω → σ → σ) (s : σ) (c₁ c₂ : List ω) :
    runChoice act s (c₁ ++ c₂) = runChoice act (runChoice act s c₁) c₂ := by
  induction c₁ generalizing s with
  | nil => rfl
  | cons o c₁ ih => exact ih (act o s)

/-- **Simulation.** If decoding commutes with one step of the action, it
commutes with running a whole choice. -/
theorem runChoice_sim {σ' ω' : Type} (act : ω → σ → σ) (act' : ω' → σ' → σ')
    (dec : σ' → σ) (enc : ω → ω')
    (hsim : ∀ o s, dec (act' (enc o) s) = act o (dec s)) :
    ∀ (c : List ω) (s : σ'), dec (runChoice act' s (c.map enc)) = runChoice act (dec s) c := by
  intro c
  induction c with
  | nil => intro s; rfl
  | cons o c ih =>
    intro s
    simp only [List.map_cons, runChoice]
    rw [ih (act' (enc o) s), hsim]

end Abstract

/-- At the list level, running a choice by filtering is `restrict`. -/
theorem runChoice_filter {α : Type} (D : List α) (c : List (Opt α)) :
    runChoice (fun o (D : List α) => D.filter o) D c = restrict D c := by
  induction c generalizing D with
  | nil => exact (restrict_nil D).symm
  | cons o c ih =>
    simp only [runChoice]
    rw [ih, restrict_cons]

end CDCert
