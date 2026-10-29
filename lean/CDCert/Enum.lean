/-
CDCert.Enum — verified enumeration of the finite family of domains defined by
one option from every constraint group.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.

Setting (deliberately abstract, so it does not depend on any particular
encoding of linear orders):

* `α` is the type of orders, with `DecidableEq α`.
* `base : List α` is the finite base universe (e.g. all linear orders on `Fin n`,
  or a restricted universe).
* A constraint group is a finite list of options; an option is a Boolean
  predicate `α → Bool` (the orders it allows). A finite subset `L : List α`
  becomes an option via `optOfList L`.
* A choice picks one option from every group (`IsChoice`). The domain of a
  choice is `base` filtered by all chosen options (`domainOf`).

Domains are always represented canonically as filters of `base`, so list
equality of domains coincides with set equality (`filter_eq_filter_iff`);
this is what makes deduplication by `=` safe.

For the Condorcet application, a group is a triple of alternatives and its
options are the never conditions admitted for that triple. Connecting this to
an order-theoretic definition of Condorcet domain is NOT done here
(see the report: it needs the never-condition characterisation).
-/
import CDCert.Dedup

namespace CDCert

/-- An option: the set of orders it allows, as a Boolean predicate. -/
abbrev Opt (α : Type) := α → Bool

/-- A constraint group: a finite list of options. -/
abbrev Group (α : Type) := List (Opt α)

section Choice
variable {ω : Type}

/-- `IsChoice c gs`: the list `c` picks exactly one option from each group of
`gs`, in order. This is the "defining assignment". The option type `ω` is
arbitrary: predicates `Opt α` at the list level, Nat masks at the bitset level. -/
inductive IsChoice : List ω → List (List ω) → Prop
  | nil : IsChoice [] []
  | cons {o : ω} {g : List ω} {os : List ω} {gs : List (List ω)} :
      o ∈ g → IsChoice os gs → IsChoice (o :: os) (g :: gs)

theorem isChoice_nil_iff {c : List ω} : IsChoice c [] ↔ c = [] := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact IsChoice.nil

theorem isChoice_cons_iff {c : List ω} {g : List ω} {gs : List (List ω)} :
    IsChoice c (g :: gs) ↔ ∃ o, o ∈ g ∧ ∃ os, IsChoice os gs ∧ c = o :: os := by
  constructor
  · intro h
    cases h with
    | cons ho hos => exact ⟨_, ho, _, hos, rfl⟩
  · rintro ⟨o, ho, os, hos, rfl⟩
    exact IsChoice.cons ho hos

theorem IsChoice.length_eq {c : List ω} {gs : List (List ω)}
    (h : IsChoice c gs) : c.length = gs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Every chosen option comes from one of the groups. -/
theorem IsChoice.exists_group {c : List ω} {gs : List (List ω)}
    (h : IsChoice c gs) : ∀ o, o ∈ c → ∃ g, g ∈ gs ∧ o ∈ g := by
  induction h with
  | nil =>
    intro o ho
    cases ho
  | cons hog _ ih =>
    intro o' ho'
    rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨_, List.mem_cons_self, hog⟩
    · obtain ⟨g', hg', hog'⟩ := ih o' ho'
      exact ⟨g', List.mem_cons_of_mem _ hg', hog'⟩

/-- Choices are preserved by renaming options. -/
theorem IsChoice.map {ω' : Type} (f : ω → ω') {c : List ω} {gs : List (List ω)}
    (h : IsChoice c gs) : IsChoice (c.map f) (gs.map (List.map f)) := by
  induction h with
  | nil => exact IsChoice.nil
  | cons ho _ ih => exact IsChoice.cons (List.mem_map_of_mem ho) ih

/-- Every choice for renamed groups is the renaming of a choice. -/
theorem IsChoice.of_map {ω' : Type} (f : ω → ω') {gs : List (List ω)} :
    ∀ {c' : List ω'}, IsChoice c' (gs.map (List.map f)) →
      ∃ c, IsChoice c gs ∧ c' = c.map f := by
  induction gs with
  | nil =>
    intro c' h
    rw [List.map_nil, isChoice_nil_iff] at h
    exact ⟨[], IsChoice.nil, h⟩
  | cons g gs ih =>
    intro c' h
    rw [List.map_cons, isChoice_cons_iff] at h
    obtain ⟨o', ho', os', hos', rfl⟩ := h
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
    obtain ⟨c, hc, rfl⟩ := ih hos'
    exact ⟨o :: c, IsChoice.cons ho hc, rfl⟩

/-- Restricting groups to sub-lists keeps choices valid. -/
theorem IsChoice.of_filter (p : ω → Bool) {gs : List (List ω)} :
    ∀ {c : List ω}, IsChoice c (gs.map (List.filter p)) → IsChoice c gs := by
  induction gs with
  | nil =>
    intro c h
    rw [List.map_nil] at h
    exact h
  | cons g gs ih =>
    intro c h
    rw [List.map_cons, isChoice_cons_iff] at h
    obtain ⟨o, ho, os, hos, rfl⟩ := h
    exact IsChoice.cons (List.mem_filter.mp ho).1 (ih hos)

/-- A choice whose options all pass `p` is a choice for the filtered groups. -/
theorem IsChoice.filter (p : ω → Bool) {c : List ω} {gs : List (List ω)}
    (h : IsChoice c gs) (hp : ∀ o, o ∈ c → p o = true) :
    IsChoice c (gs.map (List.filter p)) := by
  induction h with
  | nil => exact IsChoice.nil
  | cons ho _ ih =>
    exact IsChoice.cons (List.mem_filter.mpr ⟨ho, hp _ List.mem_cons_self⟩)
      (ih (fun o h => hp o (List.mem_cons_of_mem _ h)))

/-- All choices: the cartesian product of the groups (the naive specification). -/
def allChoices : List (List ω) → List (List ω)
  | [] => [[]]
  | g :: gs => g.flatMap (fun o => (allChoices gs).map (o :: ·))

theorem mem_allChoices (gs : List (List ω)) (c : List ω) :
    c ∈ allChoices gs ↔ IsChoice c gs := by
  induction gs generalizing c with
  | nil =>
    simp only [allChoices, List.mem_cons, List.not_mem_nil, or_false]
    exact isChoice_nil_iff.symm
  | cons g gs ih =>
    simp only [allChoices, List.mem_flatMap, List.mem_map, isChoice_cons_iff, ih]
    constructor
    · rintro ⟨o, ho, os, hos, rfl⟩
      exact ⟨o, ho, os, hos, rfl⟩
    · rintro ⟨o, ho, os, hos, rfl⟩
      exact ⟨o, ho, os, hos, rfl⟩

end Choice

section Basic
variable {α : Type}

/-- The option given by a finite subset: it allows exactly the listed orders. -/
def optOfList [DecidableEq α] (L : List α) : Opt α := fun x => decide (x ∈ L)

@[simp] theorem optOfList_eq_true [DecidableEq α] (L : List α) (x : α) :
    optOfList L x = true ↔ x ∈ L := by
  simp [optOfList]

/-- `allows c x`: the order `x` is allowed by every option in `c`. -/
def allows (c : List (Opt α)) (x : α) : Bool := c.all (fun o => o x)

theorem allows_eq_true {c : List (Opt α)} {x : α} :
    allows c x = true ↔ ∀ o, o ∈ c → o x = true := by
  simp [allows]

@[simp] theorem allows_nil (x : α) : allows ([] : List (Opt α)) x = true := rfl

theorem allows_cons (o : Opt α) (c : List (Opt α)) (x : α) :
    allows (o :: c) x = (o x && allows c x) := rfl

/-- Restrict a state (a list of orders) to the orders allowed by a choice. -/
def restrict (D : List α) (c : List (Opt α)) : List α := D.filter (allows c)

/-- The domain defined by the choice `c` inside the base universe. -/
def domainOf (base : List α) (c : List (Opt α)) : List α := restrict base c

theorem mem_restrict {D : List α} {c : List (Opt α)} {x : α} :
    x ∈ restrict D c ↔ x ∈ D ∧ ∀ o, o ∈ c → o x = true := by
  simp [restrict, List.mem_filter, allows_eq_true]

theorem mem_domainOf {base : List α} {c : List (Opt α)} {x : α} :
    x ∈ domainOf base c ↔ x ∈ base ∧ ∀ o, o ∈ c → o x = true :=
  mem_restrict

@[simp] theorem restrict_nil (D : List α) : restrict D [] = D := by
  simp [restrict, List.filter_eq_self]

/-- Restricting by `o :: c` is restricting by `o` and then by `c`. -/
theorem restrict_cons (D : List α) (o : Opt α) (c : List (Opt α)) :
    restrict D (o :: c) = restrict (D.filter o) c := by
  simp only [restrict, List.filter_filter]
  apply List.filter_congr
  intro x _
  rw [allows_cons, Bool.and_comm]

/-- Canonical form: two filters of the same list are equal iff the predicates
agree on that list. -/
theorem filter_eq_filter_iff (base : List α) (p q : α → Bool) :
    base.filter p = base.filter q ↔ ∀ x, x ∈ base → p x = q x := by
  constructor
  · intro h x hx
    have hp : x ∈ base.filter p ↔ p x = true := by simp [List.mem_filter, hx]
    have hq : x ∈ base.filter q ↔ q x = true := by simp [List.mem_filter, hx]
    rw [h] at hp
    exact Bool.eq_iff_iff.mpr (hp.symm.trans hq)
  · intro h
    exact List.filter_congr h

/-- Safe deduplication: two domains (both filters of `base`) are equal as lists
iff they have the same members. So removing `=`-duplicates merges exactly the
equal domains and never two different ones. -/
theorem domainOf_eq_iff (base : List α) (c c' : List (Opt α)) :
    domainOf base c = domainOf base c' ↔
      ∀ x, x ∈ domainOf base c ↔ x ∈ domainOf base c' := by
  unfold domainOf restrict
  rw [filter_eq_filter_iff]
  constructor
  · intro h x
    simp only [List.mem_filter]
    constructor
    · rintro ⟨hx, h1⟩
      exact ⟨hx, (h x hx) ▸ h1⟩
    · rintro ⟨hx, h1⟩
      exact ⟨hx, (h x hx).symm ▸ h1⟩
  · intro h x hx
    have hx' := h x
    simp only [List.mem_filter, hx, true_and] at hx'
    exact Bool.eq_iff_iff.mpr hx'

/-- A domain is a sublist of the base universe; in particular it inherits
`Nodup` from `base`. -/
theorem domainOf_sublist (base : List α) (c : List (Opt α)) :
    (domainOf base c).Sublist base :=
  List.filter_sublist

theorem nodup_domainOf {base : List α} (h : base.Nodup) (c : List (Opt α)) :
    (domainOf base c).Nodup :=
  (domainOf_sublist base c).nodup h

/-- Split a state by every option of one group. -/
def expand (g : Group α) (D : List α) : List (List α) := g.map (fun o => D.filter o)

theorem mem_expand {g : Group α} {D D' : List α} :
    D' ∈ expand g D ↔ ∃ o, o ∈ g ∧ D' = D.filter o := by
  simp only [expand, List.mem_map]
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

end Basic

section Enumeration
variable {α : Type} [DecidableEq α]

/-- Level-wise (breadth-first) enumeration, deduplicating the states after
every level. A state is a partial domain; its future depends only on the state
itself, which is why merging equal states is safe. -/
def enumFrom : List (Group α) → List (List α) → List (List α)
  | [], states => dedup states
  | g :: gs, states => enumFrom gs (dedup (states.flatMap (expand g)))

/-- Enumerate every domain defined by a choice, starting from `base`. -/
def enumerate (gs : List (Group α)) (base : List α) : List (List α) :=
  enumFrom gs [base]

theorem mem_enumFrom (gs : List (Group α)) (states : List (List α)) (D : List α) :
    D ∈ enumFrom gs states ↔
      ∃ S, S ∈ states ∧ ∃ c, IsChoice c gs ∧ D = restrict S c := by
  induction gs generalizing states with
  | nil =>
    simp only [enumFrom, mem_dedup, isChoice_nil_iff]
    constructor
    · intro h
      exact ⟨D, h, [], rfl, (restrict_nil D).symm⟩
    · rintro ⟨S, hS, c, rfl, rfl⟩
      simpa using hS
  | cons g gs ih =>
    simp only [enumFrom]
    rw [ih]
    constructor
    · rintro ⟨S', hS', c', hc', rfl⟩
      rw [mem_dedup, List.mem_flatMap] at hS'
      obtain ⟨S, hS, hS'⟩ := hS'
      obtain ⟨o, ho, rfl⟩ := mem_expand.mp hS'
      exact ⟨S, hS, o :: c', IsChoice.cons ho hc', (restrict_cons S o c').symm⟩
    · rintro ⟨S, hS, c, hc, rfl⟩
      obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      refine ⟨S.filter o, ?_, c', hc', restrict_cons S o c'⟩
      rw [mem_dedup, List.mem_flatMap]
      exact ⟨S, hS, mem_expand.mpr ⟨o, ho, rfl⟩⟩

/-- **Exact coverage.** The enumerator outputs exactly the domains defined by
some choice: nothing is missed and nothing else appears. -/
theorem mem_enumerate (gs : List (Group α)) (base D : List α) :
    D ∈ enumerate gs base ↔ ∃ c, IsChoice c gs ∧ D = domainOf base c := by
  simp only [enumerate, mem_enumFrom, List.mem_singleton, domainOf]
  constructor
  · rintro ⟨S, rfl, c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨base, rfl, c, hc, rfl⟩

theorem nodup_enumFrom (gs : List (Group α)) (states : List (List α)) :
    (enumFrom gs states).Nodup := by
  induction gs generalizing states with
  | nil => exact nodup_dedup _
  | cons g gs ih => exact ih _

/-- **No repetitions.** Each defined domain is listed exactly once. -/
theorem nodup_enumerate (gs : List (Group α)) (base : List α) :
    (enumerate gs base).Nodup :=
  nodup_enumFrom gs [base]

/-- Agreement with the naive specification `map (domainOf base) (allChoices gs)`. -/
theorem mem_enumerate_iff_naive (gs : List (Group α)) (base D : List α) :
    D ∈ enumerate gs base ↔ D ∈ (allChoices gs).map (domainOf base) := by
  rw [mem_enumerate, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_allChoices gs c).mpr hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_allChoices gs c).mp hc, rfl⟩

end Enumeration

section PruneDFS
variable {α : Type}

/-- A pruning test is *sound* for a goal if, whenever it fires on a state `D`
with remaining groups `gs`, no completion of `D` by a choice for `gs` meets the
goal. Only sound tests may discard states. -/
def PruneSound (prune : List (Group α) → List α → Bool) (good : List α → Bool) :
    Prop :=
  ∀ (gs : List (Group α)) (D : List α), prune gs D = true →
    ∀ c, IsChoice c gs → good (restrict D c) = false

/-- Depth-first search with pruning and a final goal filter, without
intermediate deduplication (the shape of a recursive C++ generator). -/
def dfs (prune : List (Group α) → List α → Bool) (good : List α → Bool) :
    List (Group α) → List α → List (List α)
  | [], D => if good D then [D] else []
  | g :: gs, D =>
      if prune (g :: gs) D then [] else g.flatMap (fun o => dfs prune good gs (D.filter o))

theorem mem_dfs {prune : List (Group α) → List α → Bool} {good : List α → Bool}
    (hp : PruneSound prune good) (gs : List (Group α)) (D D' : List α) :
    D' ∈ dfs prune good gs D ↔ ∃ c, IsChoice c gs ∧ D' = restrict D c ∧ good D' = true := by
  induction gs generalizing D with
  | nil =>
    simp only [dfs, isChoice_nil_iff]
    constructor
    · intro h
      split at h
      · rename_i hg
        rw [List.mem_singleton] at h
        subst h
        exact ⟨[], rfl, (restrict_nil _).symm, hg⟩
      · cases h
    · rintro ⟨c, rfl, rfl, hg⟩
      rw [restrict_nil] at hg ⊢
      rw [if_pos hg]
      exact List.mem_singleton_self _
  | cons g gs ih =>
    simp only [dfs]
    constructor
    · intro h
      split at h
      · cases h
      · rw [List.mem_flatMap] at h
        obtain ⟨o, ho, h⟩ := h
        obtain ⟨c', hc', rfl, hg⟩ := (ih (D.filter o)).mp h
        exact ⟨o :: c', IsChoice.cons ho hc', (restrict_cons D o c').symm, hg⟩
    · rintro ⟨c, hc, rfl, hg⟩
      have hnp : prune (g :: gs) D = false := by
        cases h : prune (g :: gs) D with
        | false => rfl
        | true =>
          have := hp (g :: gs) D h c hc
          rw [this] at hg
          cases hg
      rw [if_neg (by rw [hnp]; decide), List.mem_flatMap]
      obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      exact ⟨o, ho, (ih (D.filter o)).mpr ⟨c', hc', restrict_cons D o c', hg⟩⟩

end PruneDFS

section Pruned
variable {α : Type} [DecidableEq α]

/-- Level-wise enumeration with pruning and a final goal filter. -/
def enumPruneFrom (prune : List (Group α) → List α → Bool) (good : List α → Bool) :
    List (Group α) → List (List α) → List (List α)
  | [], states => dedup (states.filter good)
  | g :: gs, states =>
      enumPruneFrom prune good gs
        (dedup ((states.filter (fun D => !prune (g :: gs) D)).flatMap (expand g)))

theorem mem_enumPruneFrom {prune : List (Group α) → List α → Bool}
    {good : List α → Bool} (hp : PruneSound prune good)
    (gs : List (Group α)) (states : List (List α)) (D : List α) :
    D ∈ enumPruneFrom prune good gs states ↔
      ∃ S, S ∈ states ∧ ∃ c, IsChoice c gs ∧ D = restrict S c ∧ good D = true := by
  induction gs generalizing states with
  | nil =>
    simp only [enumPruneFrom, mem_dedup, List.mem_filter, isChoice_nil_iff]
    constructor
    · rintro ⟨hD, hg⟩
      exact ⟨D, hD, [], rfl, (restrict_nil D).symm, hg⟩
    · rintro ⟨S, hS, c, rfl, rfl, hg⟩
      rw [restrict_nil] at hg ⊢
      exact ⟨hS, hg⟩
  | cons g gs ih =>
    simp only [enumPruneFrom]
    rw [ih]
    constructor
    · rintro ⟨S', hS', c', hc', rfl, hg⟩
      rw [mem_dedup, List.mem_flatMap] at hS'
      obtain ⟨S, hS, hS'⟩ := hS'
      rw [List.mem_filter] at hS
      obtain ⟨o, ho, rfl⟩ := mem_expand.mp hS'
      refine ⟨S, hS.1, o :: c', IsChoice.cons ho hc', (restrict_cons S o c').symm, hg⟩
    · rintro ⟨S, hS, c, hc, rfl, hg⟩
      have hnp : prune (g :: gs) S = false := by
        cases h : prune (g :: gs) S with
        | false => rfl
        | true =>
          have := hp (g :: gs) S h c hc
          rw [this] at hg
          cases hg
      obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      refine ⟨S.filter o, ?_, c', hc', restrict_cons S o c', ?_⟩
      · rw [mem_dedup, List.mem_flatMap]
        refine ⟨S, ?_, mem_expand.mpr ⟨o, ho, rfl⟩⟩
        rw [List.mem_filter, hnp]
        exact ⟨hS, rfl⟩
      · exact hg

theorem nodup_enumPruneFrom (prune : List (Group α) → List α → Bool)
    (good : List α → Bool) (gs : List (Group α)) (states : List (List α)) :
    (enumPruneFrom prune good gs states).Nodup := by
  induction gs generalizing states with
  | nil => exact nodup_dedup _
  | cons g gs ih => exact ih _

end Pruned

end CDCert
