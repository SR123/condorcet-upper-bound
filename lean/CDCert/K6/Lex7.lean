/-
CDCert.K6.Lex7 — the base of the seven-level masks, and options as data.

* `base7 = copy1 ++ copy2 ++ copy3` (15120 orders of `0..6`): copy 1 lists, for each
  last label `z`, `M.map (up z) ++ [z]` for `M ∈ baseB 5`; copy 2 lists, for each first
  label `w`, `w :: M.map (up w)` for `M ∈ baseT 5`; copy 3 the same for `M ∈ baseB 5`;
* `OptD`: an option as data (no constraint, a fixed pair, a law on a triple) with its
  meaning `OptD.toOpt`; `groupsD7`: the 56 groups of `groupsEP 7` as data, triples
  `a < b < c` lexicographically then pairs `a < b` lexicographically;
* `cmpOf M`: the comparisons of an order packed into bits `7a + b` (`a < b`);
  `evalD d (cmpOf M) = d.toOpt M` on orders (`evalD_cmpOf`), so masks of options can be
  checked by the kernel from the packed comparisons (`maskOfN`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Base12
import CDCert.K6.Relabel

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

/-- Copy 1: bottom six-slices, bottom-indexed. -/
def copy1 : List (List Nat) := (List.range 7).flatMap (fun z => (baseB 5).map (fun M => M.map (up z) ++ [z]))
/-- Copy 2: top six-slices, top-indexed. -/
def copy2 : List (List Nat) := (List.range 7).flatMap (fun w => (baseT 5).map (fun M => w :: M.map (up w)))
/-- Copy 3: top six-slices, bottom-indexed. -/
def copy3 : List (List Nat) := (List.range 7).flatMap (fun w => (baseB 5).map (fun M => w :: M.map (up w)))

/-- The base of the seven-level masks. -/
def base7 : List (List Nat) := copy1 ++ copy2 ++ copy3

/-- An option as data. -/
inductive OptD where
  | top : OptD
  | pr (a b : Nat) : OptD
  | law (a b c : Nat) (l : Fin 3 × Fin 3) : OptD

/-- The meaning of an option. -/
def OptD.toOpt : OptD → Opt (List Nat)
  | .top => fun _ => true
  | .pr a b => pairL a b
  | .law a b c l => holdsL a b c l

/-- The 56 groups of `groupsEP 7` as data: triples lexicographically, then pairs. -/
def groupsD7 : List (List OptD) :=
  (triplesN 7).map (fun t => lawsExtreme.map (OptD.law t.1 t.2.1 t.2.2)) ++
  (pairsN 7).map (fun ab => [OptD.top, OptD.pr ab.1 ab.2, OptD.pr ab.2 ab.1])

/-- Packed comparisons of an order: bit `7a + b` is `before a b` (`a < b < 7`). -/
def cmpOf (M : List Nat) : Nat :=
  (pairsN 7).foldr (fun ab acc => acc ||| (if before ab.1 ab.2 M then 1 <<< (7 * ab.1 + ab.2) else 0)) 0

/-- Comparison read from packed bits. -/
def cmpB (cm a b : Nat) : Bool := if a < b then cm.testBit (7 * a + b) else !(cm.testBit (7 * b + a))

/-- `neverL` from packed comparisons. -/
def nvB (cm x y z : Nat) (p : Fin 3) : Bool :=
  if p = 0 then !(cmpB cm x y && cmpB cm x z)
  else if p = 1 then (cmpB cm x y == cmpB cm x z)
  else (cmpB cm x y || cmpB cm x z)

/-- An option evaluated on packed comparisons. -/
def evalD (d : OptD) (cm : Nat) : Bool :=
  match d with
  | .top => true
  | .pr a b => cmpB cm a b
  | .law a b c l =>
    if l.1 = 0 then nvB cm a b c l.2 else if l.1 = 1 then nvB cm b a c l.2 else nvB cm c a b l.2

/-- Mask over a list of packed comparisons. -/
def maskOfN : List Nat → (Nat → Bool) → Nat
  | [], _ => 0
  | x :: xs, t => 2 * maskOfN xs t + (if t x then 1 else 0)

theorem maskOfN_map (base : List (List Nat)) (f : List Nat → Nat) (t : Nat → Bool) :
    maskOfN (base.map f) t = maskOf base (fun M => t (f M)) := by
  induction base with
  | nil => rfl
  | cons M base ih => simp only [List.map_cons, maskOfN, maskOf, ih]

/-! ### Packed comparisons are comparisons -/

theorem testBit_foldr_cmp (M : List Nat) (i : Nat) : ∀ (ps : List (Nat × Nat)),
    (ps.foldr (fun ab acc => acc ||| (if before ab.1 ab.2 M then 1 <<< (7 * ab.1 + ab.2) else 0)) 0).testBit i =
      ps.any (fun ab => before ab.1 ab.2 M && decide (7 * ab.1 + ab.2 = i))
  | [] => by simp
  | ab :: ps => by
    rw [List.foldr_cons, Nat.testBit_or, testBit_foldr_cmp M i ps, List.any_cons]
    split
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      rename_i h
      simp [h, Bool.or_comm]
    · rename_i h
      simp [h]

theorem mem_pairsN {n : Nat} {ab : Nat × Nat} : ab ∈ pairsN n ↔ ab.1 < ab.2 ∧ ab.2 < n := by
  obtain ⟨a, b⟩ := ab
  simp only [pairsN, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a', ha, b', hb, h⟩
    split at h
    · rename_i hlt
      rw [List.mem_singleton] at h
      cases h
      exact ⟨hlt, hb⟩
    · cases h
  · rintro ⟨h1, h2⟩
    refine ⟨a, by omega, b, h2, ?_⟩
    rw [if_pos h1]
    exact List.mem_singleton_self _

theorem testBit_cmpOf {M : List Nat} {a b : Nat} (hab : a < b) (hb : b < 7) :
    (cmpOf M).testBit (7 * a + b) = before a b M := by
  unfold cmpOf
  rw [testBit_foldr_cmp]
  cases h : before a b M
  · rw [List.any_eq_false]
    intro ab hab' hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    have hm := mem_pairsN.mp hab'
    have e1 : ab.1 = a ∧ ab.2 = b := by omega
    obtain ⟨a', b'⟩ := ab
    simp only at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [h] at h1
    cases h1
  · rw [List.any_eq_true]
    exact ⟨(a, b), mem_pairsN.mpr ⟨hab, hb⟩, by simp [h]⟩

theorem cmpB_cmpOf {M : List Nat} (hM : M ∈ orders 7) {a b : Nat} (ha : a < 7) (hb : b < 7)
    (hab : a ≠ b) : cmpB (cmpOf M) a b = before a b M := by
  unfold cmpB
  by_cases h : a < b
  · rw [if_pos h, testBit_cmpOf h hb]
  · rw [if_neg h, testBit_cmpOf (by omega) ha]
    rw [before_eq_not (nodup_of_mem_orders hM) ((mem_of_mem_orders hM a).mpr ha)
      ((mem_of_mem_orders hM b).mpr hb) hab]

/-- Options with labels `< 7` (distinct where it matters). -/
def OptD.WF : OptD → Prop
  | .top => True
  | .pr a b => a < 7 ∧ b < 7 ∧ a ≠ b
  | .law a b c _ => a < b ∧ b < c ∧ c < 7

theorem evalD_cmpOf {d : OptD} (hd : d.WF) {M : List Nat} (hM : M ∈ orders 7) :
    evalD d (cmpOf M) = d.toOpt M := by
  cases d with
  | top => rfl
  | pr a b =>
    obtain ⟨ha, hb, hab⟩ := hd
    exact cmpB_cmpOf hM ha hb hab
  | law a b c l =>
    obtain ⟨h1, h2, h3⟩ := hd
    have nv : ∀ x y z (p : Fin 3), x < 7 → y < 7 → z < 7 → x ≠ y → x ≠ z →
        nvB (cmpOf M) x y z p = neverL x y z p M := by
      intro x y z p hx hy hz hxy hxz
      unfold nvB neverL
      rw [cmpB_cmpOf hM hx hy hxy, cmpB_cmpOf hM hx hz hxz]
    show (if l.1 = 0 then nvB (cmpOf M) a b c l.2 else if l.1 = 1 then nvB (cmpOf M) b a c l.2
      else nvB (cmpOf M) c a b l.2) = holdsL a b c l M
    unfold holdsL
    split
    · rw [nv a b c l.2 (by omega) (by omega) (by omega) (by omega) (by omega)]
    · split
      · rw [nv b a c l.2 (by omega) (by omega) (by omega) (by omega) (by omega)]
      · rw [nv c a b l.2 (by omega) (by omega) (by omega) (by omega) (by omega)]

theorem groupsD7_wf : ∀ g, g ∈ groupsD7 → ∀ d, d ∈ g → d.WF := by
  intro g hg d hd
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hd
    exact mem_triplesN.mp ht
  · obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
    have := mem_pairsN.mp hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · trivial
    · exact ⟨by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega⟩

end CDCert.K6
