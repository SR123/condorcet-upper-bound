/-
CDCert.Slice — the coverage steps of the case generator:

1. keep only options that contain a required endpoint slice `S`;
2. keep only domains whose endpoint slice is exactly `S`;
3. prune a partial state only when some forbidden endpoint order (an order in
   the endpoint region `E` but not in `S`) is still present and every option of
   every remaining group retains it.

Each step is proved sound and complete: the generator with all three steps
outputs exactly the domains defined by a choice whose `E`-slice is exactly `S`,
without repetitions (breadth-first form `enumerateExact`, depth-first form
`enumerateExactDFS`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.

Abstract parameters:
* `E : α → Bool` — the endpoint region (e.g. "the deleted alternative is ranked
  first"); its meaning is fixed by whoever instantiates it.
* `S : List α` — the required slice (normally `S ⊆ E`, see `exactSlice_iff`).
-/
import CDCert.Enum

namespace CDCert

section RequiredSlice
variable {α : Type}

/-- Keep only the options of a group that allow every order of `S`. -/
def keepContaining (S : List α) (g : Group α) : Group α :=
  g.filter (fun o => S.all o)

/-- Apply `keepContaining S` to every group. -/
def requireSlice (S : List α) (gs : List (Group α)) : List (Group α) :=
  gs.map (keepContaining S)

theorem mem_keepContaining {S : List α} {g : Group α} {o : Opt α} :
    o ∈ keepContaining S g ↔ o ∈ g ∧ ∀ s, s ∈ S → o s = true := by
  simp [keepContaining, List.mem_filter, List.all_eq_true]

/-- Choices for the filtered groups are exactly the choices whose options all
contain `S`. -/
theorem isChoice_requireSlice {S : List α} {gs : List (Group α)} {c : List (Opt α)} :
    IsChoice c (requireSlice S gs) ↔
      IsChoice c gs ∧ ∀ o, o ∈ c → ∀ s, s ∈ S → o s = true := by
  induction gs generalizing c with
  | nil =>
    simp only [requireSlice, List.map_nil, isChoice_nil_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, fun o ho => by cases ho⟩
    · rintro ⟨rfl, _⟩
      rfl
  | cons g gs ih =>
    simp only [requireSlice, List.map_cons] at ih ⊢
    rw [isChoice_cons_iff, isChoice_cons_iff]
    constructor
    · rintro ⟨o, ho, os, hos, rfl⟩
      rw [mem_keepContaining] at ho
      obtain ⟨hos', hall⟩ := ih.mp hos
      refine ⟨⟨o, ho.1, os, hos', rfl⟩, ?_⟩
      intro o' ho'
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact ho.2
      · exact hall o' ho'
    · rintro ⟨⟨o, ho, os, hos, rfl⟩, hall⟩
      refine ⟨o, mem_keepContaining.mpr ⟨ho, hall o List.mem_cons_self⟩, os, ?_, rfl⟩
      exact ih.mpr ⟨hos, fun o' ho' => hall o' (List.mem_cons_of_mem _ ho')⟩

/-- `S` survives a restriction iff it was present and every chosen option
contains it. -/
theorem subset_restrict_iff {S D : List α} {c : List (Opt α)} :
    (∀ s, s ∈ S → s ∈ restrict D c) ↔
      (∀ s, s ∈ S → s ∈ D) ∧ ∀ o, o ∈ c → ∀ s, s ∈ S → o s = true := by
  simp only [mem_restrict]
  constructor
  · intro h
    exact ⟨fun s hs => (h s hs).1, fun o ho s hs => (h s hs).2 o ho⟩
  · rintro ⟨h1, h2⟩ s hs
    exact ⟨h1 s hs, fun o ho => h2 o ho s hs⟩

variable [DecidableEq α]

/-- **Required slice, sound and complete.** If `S ⊆ base`, enumerating with
the filtered groups yields exactly the defined domains that contain `S`. -/
theorem mem_enumerate_requireSlice {S base : List α} (hS : ∀ s, s ∈ S → s ∈ base)
    (gs : List (Group α)) (D : List α) :
    D ∈ enumerate (requireSlice S gs) base ↔
      ∃ c, IsChoice c gs ∧ D = domainOf base c ∧ ∀ s, s ∈ S → s ∈ D := by
  rw [mem_enumerate]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hc', hall⟩ := isChoice_requireSlice.mp hc
    exact ⟨c, hc', rfl, subset_restrict_iff.mpr ⟨hS, hall⟩⟩
  · rintro ⟨c, hc, rfl, hsub⟩
    exact ⟨c, isChoice_requireSlice.mpr ⟨hc, (subset_restrict_iff.mp hsub).2⟩, rfl⟩

/-- Without `S ⊆ base` nothing contains `S`; the filtered enumeration then
still only produces defined domains (soundness needs no hypothesis). -/
theorem mem_enumerate_requireSlice_sound {S base : List α} {gs : List (Group α)}
    {D : List α} (h : D ∈ enumerate (requireSlice S gs) base) :
    ∃ c, IsChoice c gs ∧ D = domainOf base c ∧ ∀ o, o ∈ c → ∀ s, s ∈ S → o s = true := by
  obtain ⟨c, hc, rfl⟩ := (mem_enumerate _ _ _).mp h
  obtain ⟨hc', hall⟩ := isChoice_requireSlice.mp hc
  exact ⟨c, hc', rfl, hall⟩

end RequiredSlice

section ExactSlice
variable {α : Type} [DecidableEq α]

/-- `D` has exact `E`-slice `S`: every order of `S` is in `D`, and every
`E`-order of `D` is in `S`. -/
def ExactSlice (E : α → Bool) (S D : List α) : Prop :=
  (∀ s, s ∈ S → s ∈ D) ∧ ∀ x, x ∈ D → E x = true → x ∈ S

/-- Boolean test for `ExactSlice`. -/
def exactSliceB (E : α → Bool) (S D : List α) : Bool :=
  S.all (fun s => decide (s ∈ D)) && D.all (fun x => !E x || decide (x ∈ S))

theorem exactSliceB_eq_true {E : α → Bool} {S D : List α} :
    exactSliceB E S D = true ↔ ExactSlice E S D := by
  unfold exactSliceB ExactSlice
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx hE => ?_⟩
    rcases h2 x hx with h | h
    · rw [hE] at h
      cases h
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx => ?_⟩
    cases hE : E x with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h2 x hx hE)

omit [DecidableEq α] in
/-- When `S` consists of `E`-orders, exactness says that the `E`-orders of `D`
are precisely the orders of `S`. -/
theorem exactSlice_iff {E : α → Bool} {S D : List α} (hSE : ∀ s, s ∈ S → E s = true) :
    ExactSlice E S D ↔ ∀ x, (x ∈ D ∧ E x = true) ↔ x ∈ S := by
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun h => h2 x h.1 h.2, fun h => ⟨h1 x h, hSE x h⟩⟩
  · intro h
    exact ⟨fun s hs => ((h s).mpr hs).1, fun x hx hE => (h x).mp ⟨hx, hE⟩⟩

/-- Every option of every remaining group retains `t`. -/
def mustRetain (gs : List (Group α)) (t : α) : Bool :=
  gs.all (fun g => g.all (fun o => o t))

omit [DecidableEq α] in
theorem mustRetain_eq_true {gs : List (Group α)} {t : α} :
    mustRetain gs t = true ↔ ∀ g, g ∈ gs → ∀ o, o ∈ g → o t = true := by
  simp [mustRetain, List.all_eq_true]

/-- The pruning test: some forbidden endpoint order (in `E`, not in `S`) is in
the current state and is retained by every option of every remaining group. -/
def pruneForbidden (E : α → Bool) (S : List α) (gs : List (Group α)) (D : List α) : Bool :=
  D.any (fun t => E t && !decide (t ∈ S) && mustRetain gs t)

theorem pruneForbidden_eq_true {E : α → Bool} {S : List α} {gs : List (Group α)}
    {D : List α} :
    pruneForbidden E S gs D = true ↔
      ∃ t, t ∈ D ∧ E t = true ∧ t ∉ S ∧ mustRetain gs t = true := by
  simp only [pruneForbidden, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨t, ht, ⟨hE, hS⟩, hm⟩
    exact ⟨t, ht, hE, hS, hm⟩
  · rintro ⟨t, ht, hE, hS, hm⟩
    exact ⟨t, ht, ⟨hE, hS⟩, hm⟩

omit [DecidableEq α] in
/-- An order retained by every option of every remaining group survives any
completion. -/
theorem mem_restrict_of_mustRetain {gs : List (Group α)} {t : α} {D : List α}
    {c : List (Opt α)} (hm : mustRetain gs t = true) (hc : IsChoice c gs) (ht : t ∈ D) :
    t ∈ restrict D c := by
  rw [mem_restrict]
  refine ⟨ht, fun o ho => ?_⟩
  obtain ⟨g, hg, hog⟩ := hc.exists_group o ho
  exact mustRetain_eq_true.mp hm g hg o hog

/-- **The pruning step is sound**: when it fires, no completion has exact
`E`-slice `S`. -/
theorem pruneForbidden_sound (E : α → Bool) (S : List α) :
    PruneSound (pruneForbidden E S) (exactSliceB E S) := by
  intro gs D hp c hc
  obtain ⟨t, ht, hE, hS, hm⟩ := pruneForbidden_eq_true.mp hp
  cases h : exactSliceB E S (restrict D c) with
  | false => rfl
  | true =>
    exact absurd ((exactSliceB_eq_true.mp h).2 t (mem_restrict_of_mustRetain hm hc ht) hE) hS

/-- The generator: required-slice option filtering, forbidden-order pruning,
exact-slice filtering, level-wise deduplication. -/
def enumerateExact (E : α → Bool) (S : List α) (gs : List (Group α)) (base : List α) :
    List (List α) :=
  enumPruneFrom (pruneForbidden E S) (exactSliceB E S) (requireSlice S gs) [base]

/-- The same generator in depth-first form, deduplicated once at the end. -/
def enumerateExactDFS (E : α → Bool) (S : List α) (gs : List (Group α)) (base : List α) :
    List (List α) :=
  dedup (dfs (pruneForbidden E S) (exactSliceB E S) (requireSlice S gs) base)

/-- Shared step: the choices for the filtered groups that give an exact-slice
domain are exactly the choices for the original groups that do so. -/
theorem exists_requireSlice_exact_iff {E : α → Bool} {S : List α} {gs : List (Group α)}
    {base D : List α} :
    (∃ c, IsChoice c (requireSlice S gs) ∧ D = restrict base c ∧ exactSliceB E S D = true) ↔
      ∃ c, IsChoice c gs ∧ D = domainOf base c ∧ ExactSlice E S D := by
  constructor
  · rintro ⟨c, hc, rfl, hx⟩
    exact ⟨c, (isChoice_requireSlice.mp hc).1, rfl, exactSliceB_eq_true.mp hx⟩
  · rintro ⟨c, hc, rfl, hx⟩
    refine ⟨c, isChoice_requireSlice.mpr ⟨hc, ?_⟩, rfl, exactSliceB_eq_true.mpr hx⟩
    exact (subset_restrict_iff.mp hx.1).2

/-- **Main coverage theorem (breadth-first form).** The generator outputs
exactly the domains defined by a choice whose `E`-slice is exactly `S`. No
hypothesis on `S`, `E` or `base` is needed. -/
theorem mem_enumerateExact (E : α → Bool) (S : List α) (gs : List (Group α))
    (base D : List α) :
    D ∈ enumerateExact E S gs base ↔
      ∃ c, IsChoice c gs ∧ D = domainOf base c ∧ ExactSlice E S D := by
  unfold enumerateExact
  rw [mem_enumPruneFrom (pruneForbidden_sound E S), ← exists_requireSlice_exact_iff]
  simp only [List.mem_singleton]
  constructor
  · rintro ⟨S', rfl, c, hc, rfl, hx⟩
    exact ⟨c, hc, rfl, hx⟩
  · rintro ⟨c, hc, rfl, hx⟩
    exact ⟨base, rfl, c, hc, rfl, hx⟩

theorem nodup_enumerateExact (E : α → Bool) (S : List α) (gs : List (Group α))
    (base : List α) : (enumerateExact E S gs base).Nodup :=
  nodup_enumPruneFrom _ _ _ _

/-- **Main coverage theorem (depth-first form).** -/
theorem mem_enumerateExactDFS (E : α → Bool) (S : List α) (gs : List (Group α))
    (base D : List α) :
    D ∈ enumerateExactDFS E S gs base ↔
      ∃ c, IsChoice c gs ∧ D = domainOf base c ∧ ExactSlice E S D := by
  unfold enumerateExactDFS
  rw [mem_dedup, mem_dfs (pruneForbidden_sound E S), exists_requireSlice_exact_iff]

theorem nodup_enumerateExactDFS (E : α → Bool) (S : List α) (gs : List (Group α))
    (base : List α) : (enumerateExactDFS E S gs base).Nodup :=
  nodup_dedup _

/-- The two generators produce the same family. -/
theorem mem_enumerateExact_iff_DFS (E : α → Bool) (S : List α) (gs : List (Group α))
    (base D : List α) :
    D ∈ enumerateExact E S gs base ↔ D ∈ enumerateExactDFS E S gs base := by
  rw [mem_enumerateExact, mem_enumerateExactDFS]

/-- The generator agrees with filtering the unpruned enumeration by exactness. -/
theorem mem_enumerateExact_iff_filter (E : α → Bool) (S : List α) (gs : List (Group α))
    (base D : List α) :
    D ∈ enumerateExact E S gs base ↔ D ∈ (enumerate gs base).filter (exactSliceB E S) := by
  rw [mem_enumerateExact, List.mem_filter, mem_enumerate, exactSliceB_eq_true]
  constructor
  · rintro ⟨c, hc, rfl, hx⟩
    exact ⟨⟨c, hc, rfl⟩, hx⟩
  · rintro ⟨⟨c, hc, rfl⟩, hx⟩
    exact ⟨c, hc, rfl, hx⟩

end ExactSlice

end CDCert
