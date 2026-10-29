/-
CDCert.ListOrders — the list side of the order/list bridge.

Agreed finite base: `CDCert.Examples.orders n`, the permutations of
`List.range n`, each read from top to bottom.

* `before a b L` — `a` occurs in `L` and `b` occurs after it. This is the list
  reading of `Condorcet.Order`'s `r a b = true` ("a is above b").
* On duplicate-free lists `before` is irreflexive, transitive, asymmetric and
  total on members; it is invariant under filtering (deleting other labels)
  and under injective relabelling; and a duplicate-free list is determined by
  its members and its `before` relation (`eq_of_before_eq`).
* `mem_orders_iff`: `L ∈ orders n ↔ L.Perm (List.range n)` (completeness of
  `perms` as well as soundness).
* `neverL` / `holdsL` / `pairL` are written clause by clause like
  `Condorcet.Never` / `Condorcet.HoldsLaw` and a fixed pair, so the Mathlib
  bridge (`CDCert/Bridge.lean`) can identify them by unfolding.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.PermsNodup

namespace CDCert.ListOrder

open CDCert CDCert.Examples

/-! ### `before` -/

section Before
variable {β : Type} [DecidableEq β]

/-- `before a b L`: `a` occurs in `L` and `b` occurs after it. -/
def before (a b : β) : List β → Bool
  | [] => false
  | y :: ys => if y = a then decide (b ∈ ys) else if y = b then false else before a b ys

theorem before_cons (a b y : β) (ys : List β) :
    before a b (y :: ys) =
      (if y = a then decide (b ∈ ys) else if y = b then false else before a b ys) := rfl

theorem mem_of_before {a b : β} : ∀ {L : List β}, before a b L = true → a ∈ L ∧ b ∈ L
  | [], h => by cases h
  | y :: ys, h => by
    rw [before_cons] at h
    by_cases hya : y = a
    · rw [if_pos hya] at h
      subst hya
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (of_decide_eq_true h)⟩
    · rw [if_neg hya] at h
      by_cases hyb : y = b
      · rw [if_pos hyb] at h
        cases h
      · rw [if_neg hyb] at h
        obtain ⟨h1, h2⟩ := mem_of_before h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem before_eq_false_of_not_mem_left {a b : β} {L : List β} (h : a ∉ L) :
    before a b L = false := by
  cases hb : before a b L with
  | false => rfl
  | true => exact absurd (mem_of_before hb).1 h

theorem before_eq_false_of_not_mem_right {a b : β} {L : List β} (h : b ∉ L) :
    before a b L = false := by
  cases hb : before a b L with
  | false => rfl
  | true => exact absurd (mem_of_before hb).2 h

theorem before_self {a : β} : ∀ {L : List β}, L.Nodup → before a a L = false
  | [], _ => rfl
  | y :: ys, h => by
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp h
    rw [before_cons]
    by_cases hya : y = a
    · rw [if_pos hya]
      subst hya
      exact decide_eq_false hy
    · rw [if_neg hya, if_neg hya]
      exact before_self hys

theorem before_trans {a b c : β} : ∀ {L : List β}, L.Nodup →
    before a b L = true → before b c L = true → before a c L = true
  | [], _, h, _ => by cases h
  | y :: ys, hnd, hab, hbc => by
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp hnd
    rw [before_cons] at hab hbc ⊢
    by_cases hya : y = a
    · subst hya
      rw [if_pos rfl] at hab ⊢
      have hb : b ∈ ys := of_decide_eq_true hab
      have hyb : y ≠ b := fun h => hy (h ▸ hb)
      rw [if_neg hyb] at hbc
      by_cases hyc : y = c
      · rw [if_pos hyc] at hbc
        cases hbc
      · rw [if_neg hyc] at hbc
        exact decide_eq_true (mem_of_before hbc).2
    · rw [if_neg hya] at hab ⊢
      by_cases hyb : y = b
      · rw [if_pos hyb] at hab
        cases hab
      · rw [if_neg hyb] at hab hbc
        by_cases hyc : y = c
        · rw [if_pos hyc] at hbc
          cases hbc
        · rw [if_neg hyc] at hbc ⊢
          exact before_trans hys hab hbc

theorem before_asymm {a b : β} {L : List β} (hnd : L.Nodup) (h : before a b L = true) :
    before b a L = false := by
  cases hba : before b a L with
  | false => rfl
  | true =>
    have := before_trans hnd h hba
    rw [before_self hnd] at this
    cases this

theorem before_total {a b : β} : ∀ {L : List β}, a ∈ L → b ∈ L → a ≠ b →
    before a b L = true ∨ before b a L = true
  | [], ha, _, _ => by cases ha
  | y :: ys, ha, hb, hab => by
    rw [before_cons, before_cons]
    by_cases hya : y = a
    · subst hya
      left
      rw [if_pos rfl]
      rcases List.mem_cons.mp hb with h | h
      · exact absurd h.symm hab
      · exact decide_eq_true h
    · by_cases hyb : y = b
      · subst hyb
        right
        rw [if_pos rfl]
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hya
        · exact decide_eq_true h
      · rw [if_neg hya, if_neg hyb, if_neg hyb, if_neg hya]
        have ha' : a ∈ ys := (List.mem_cons.mp ha).resolve_left (fun h => hya h.symm)
        have hb' : b ∈ ys := (List.mem_cons.mp hb).resolve_left (fun h => hyb h.symm)
        exact before_total ha' hb' hab

/-- Deleting other labels does not change `before`. -/
theorem before_filter (p : β → Bool) {a b : β} (ha : p a = true) (hb : p b = true) :
    ∀ (L : List β), before a b (L.filter p) = before a b L
  | [] => rfl
  | y :: ys => by
    rw [List.filter_cons]
    by_cases hy : p y = true
    · rw [if_pos hy, before_cons, before_cons, before_filter p ha hb ys]
      have hmem : decide (b ∈ ys.filter p) = decide (b ∈ ys) := by
        simp [List.mem_filter, hb]
      rw [hmem]
    · rw [if_neg hy, before_filter p ha hb ys, before_cons]
      have hya : y ≠ a := fun h => hy (h ▸ ha)
      have hyb : y ≠ b := fun h => hy (h ▸ hb)
      rw [if_neg hya, if_neg hyb]

/-- Injective relabelling does not change `before`. -/
theorem before_map {γ : Type} [DecidableEq γ] (f : β → γ) (hf : Function.Injective f) (a b : β) :
    ∀ (L : List β), before (f a) (f b) (L.map f) = before a b L
  | [] => rfl
  | y :: ys => by
    rw [List.map_cons, before_cons, before_cons, before_map f hf a b ys]
    have e1 : (f y = f a) ↔ (y = a) := ⟨fun h => hf h, fun h => h ▸ rfl⟩
    have e2 : (f y = f b) ↔ (y = b) := ⟨fun h => hf h, fun h => h ▸ rfl⟩
    have e3 : decide (f b ∈ ys.map f) = decide (b ∈ ys) := by
      apply decide_eq_decide.mpr
      constructor
      · intro h
        obtain ⟨z, hz, hzb⟩ := List.mem_map.mp h
        exact hf hzb ▸ hz
      · intro h
        exact List.mem_map_of_mem h
    by_cases hya : y = a
    · rw [if_pos (e1.mpr hya), if_pos hya, e3]
    · rw [if_neg (fun h => hya (e1.mp h)), if_neg hya]
      by_cases hyb : y = b
      · rw [if_pos (e2.mpr hyb), if_pos hyb]
      · rw [if_neg (fun h => hyb (e2.mp h)), if_neg hyb]

/-- A list sorted by `R` has `R a b` whenever `a` comes before `b`. -/
theorem rel_of_before {R : β → β → Prop} {a b : β} :
    ∀ {L : List β}, L.Pairwise R → before a b L = true → R a b
  | [], _, h => by cases h
  | y :: ys, hp, h => by
    rw [List.pairwise_cons] at hp
    rw [before_cons] at h
    by_cases hya : y = a
    · rw [if_pos hya] at h
      subst hya
      exact hp.1 b (of_decide_eq_true h)
    · rw [if_neg hya] at h
      by_cases hyb : y = b
      · rw [if_pos hyb] at h
        cases h
      · rw [if_neg hyb] at h
        exact rel_of_before hp.2 h

/-- A duplicate-free list is determined by its members and its `before` relation. -/
theorem eq_of_before_eq : ∀ {L₁ L₂ : List β}, L₁.Nodup → L₂.Nodup →
    (∀ x, x ∈ L₁ ↔ x ∈ L₂) → (∀ a b, before a b L₁ = before a b L₂) → L₁ = L₂
  | [], [], _, _, _, _ => rfl
  | [], y :: _, _, _, hm, _ => absurd ((hm y).mpr List.mem_cons_self) List.not_mem_nil
  | x :: _, [], _, _, hm, _ => absurd ((hm x).mp List.mem_cons_self) List.not_mem_nil
  | x :: xs, y :: ys, h₁, h₂, hm, hb => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h₁
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp h₂
    have hxy : x = y := by
      refine Decidable.byContradiction fun hne => ?_
      have hyxs : y ∈ xs :=
        (List.mem_cons.mp ((hm y).mpr List.mem_cons_self)).resolve_left (fun h => hne h.symm)
      have h1 : before x y (x :: xs) = true := by
        rw [before_cons, if_pos rfl]
        exact decide_eq_true hyxs
      have h2 : before x y (y :: ys) = false := by
        rw [before_cons, if_neg (fun h => hne h.symm), if_pos rfl]
      rw [hb x y, h2] at h1
      cases h1
    subst hxy
    congr 1
    apply eq_of_before_eq hxs hys
    · intro z
      constructor
      · intro hz
        have hzx : z ≠ x := fun h => hx (h ▸ hz)
        exact (List.mem_cons.mp ((hm z).mp (List.mem_cons_of_mem _ hz))).resolve_left hzx
      · intro hz
        have hzx : z ≠ x := fun h => hy (h ▸ hz)
        exact (List.mem_cons.mp ((hm z).mpr (List.mem_cons_of_mem _ hz))).resolve_left hzx
    · intro a b
      by_cases hax : a = x
      · subst hax
        rw [before_eq_false_of_not_mem_left hx, before_eq_false_of_not_mem_left hy]
      · by_cases hbx : b = x
        · subst hbx
          rw [before_eq_false_of_not_mem_right hx, before_eq_false_of_not_mem_right hy]
        · have := hb a b
          rw [before_cons, before_cons, if_neg (fun h => hax h.symm),
            if_neg (fun h => hbx h.symm), if_neg (fun h => hax h.symm),
            if_neg (fun h => hbx h.symm)] at this
          exact this

end Before

/-! ### The agreed base: completeness of `perms` -/

theorem mem_insertAll_append (x : Nat) :
    ∀ (p₁ p₂ : List Nat), p₁ ++ x :: p₂ ∈ insertAll x (p₁ ++ p₂)
  | [], [] => List.mem_singleton_self _
  | [], _ :: _ => List.mem_cons_self
  | z :: p₁, p₂ => by
    show z :: (p₁ ++ x :: p₂) ∈ insertAll x (z :: (p₁ ++ p₂))
    simp only [insertAll]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_insertAll_append x p₁ p₂))

theorem perm_of_mem_insertAll (x : Nat) :
    ∀ {l p : List Nat}, p ∈ insertAll x l → p.Perm (x :: l)
  | [], p, h => by
    simp only [insertAll, List.mem_singleton] at h
    subst h
    exact List.Perm.refl _
  | z :: zs, p, h => by
    simp only [insertAll, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact List.Perm.refl _
    · exact ((perm_of_mem_insertAll x hq).cons z).trans (List.Perm.swap x z zs)

theorem perm_of_mem_perms : ∀ {l p : List Nat}, p ∈ perms l → p.Perm l
  | [], p, h => by
    simp only [perms, List.mem_singleton] at h
    subst h
    exact List.Perm.refl _
  | x :: xs, p, h => by
    simp only [perms, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    exact (perm_of_mem_insertAll x hp).trans ((perm_of_mem_perms hq).cons x)

theorem mem_perms_of_perm : ∀ {l p : List Nat}, p.Perm l → p ∈ perms l
  | [], p, h => by
    rw [List.perm_nil] at h
    subst h
    exact List.mem_singleton_self _
  | x :: xs, p, h => by
    have hx : x ∈ p := h.symm.mem_iff.mp List.mem_cons_self
    obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hx
    have h' : (p₁ ++ p₂).Perm xs := (List.perm_middle.symm.trans h).cons_inv
    simp only [perms, List.mem_flatMap]
    exact ⟨p₁ ++ p₂, mem_perms_of_perm h', mem_insertAll_append x p₁ p₂⟩

theorem mem_perms_iff {l p : List Nat} : p ∈ perms l ↔ p.Perm l :=
  ⟨perm_of_mem_perms, mem_perms_of_perm⟩

/-- **The agreed base.** `orders n` is exactly the set of permutations of `range n`. -/
theorem mem_orders_iff {n : Nat} {L : List Nat} : L ∈ orders n ↔ L.Perm (List.range n) :=
  mem_perms_iff

theorem nodup_of_mem_orders {n : Nat} {L : List Nat} (h : L ∈ orders n) : L.Nodup :=
  (mem_orders_iff.mp h).nodup_iff.mpr List.nodup_range

theorem mem_of_mem_orders {n : Nat} {L : List Nat} (h : L ∈ orders n) (a : Nat) :
    a ∈ L ↔ a < n := by
  rw [(mem_orders_iff.mp h).mem_iff, List.mem_range]

/-! ### Laws, written like `Condorcet.Never` / `Condorcet.HoldsLaw` -/

/-- `x N p` on the triple `{x, y, z}`, in the comparisons of `x` with `y` and `z`
(positions 0, 1, 2 = first, middle, last), exactly as `Condorcet.Never`. -/
def neverL (x y z : Nat) (p : Fin 3) : Opt (List Nat) := fun L =>
  if p = 0 then !(before x y L && before x z L)
  else if p = 1 then (before x y L == before x z L)
  else (before x y L || before x z L)

/-- The law `law = (element, position)` on the increasing triple `(a, b, c)`,
exactly as `Condorcet.HoldsLaw` (element 0, 1, 2 = smallest, middle, largest). -/
def holdsL (a b c : Nat) (law : Fin 3 × Fin 3) : Opt (List Nat) :=
  if law.1 = 0 then neverL a b c law.2
  else if law.1 = 1 then neverL b a c law.2
  else neverL c a b law.2

/-- Fixed pair: `a` above `b`. -/
def pairL (a b : Nat) : Opt (List Nat) := fun L => before a b L

/-- All nine laws, and the six extreme laws (positions first and last). -/
def lawsAll : List (Fin 3 × Fin 3) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def lawsExtreme : List (Fin 3 × Fin 3) := [(0, 0), (0, 2), (1, 0), (1, 2), (2, 0), (2, 2)]

theorem mem_lawsAll (law : Fin 3 × Fin 3) : law ∈ lawsAll := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := law
  have h1 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h2 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    simp [lawsAll, Prod.ext_iff, Fin.ext_iff]

/-- Increasing triples `a < b < c < n`, lexicographically. -/
def triplesN (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (List.range n).flatMap fun c => if a < b ∧ b < c then [(a, b, c)] else []

theorem mem_triplesN {n : Nat} {t : Nat × Nat × Nat} :
    t ∈ triplesN n ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < n := by
  obtain ⟨a, b, c⟩ := t
  simp only [triplesN, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, h⟩
    split at h
    · rename_i hlt
      rw [List.mem_singleton] at h
      cases h
      exact ⟨hlt.1, hlt.2, hc⟩
    · cases h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨a, by omega, b, by omega, c, h3, ?_⟩
    rw [if_pos ⟨h1, h2⟩]
    exact List.mem_singleton_self _

/-- Groups for full domains: one group per increasing triple, all nine laws. -/
def groupsFull (n : Nat) : List (Group (List Nat)) :=
  (triplesN n).map fun t => lawsAll.map (holdsL t.1 t.2.1 t.2.2)

/-- Groups for extreme laws plus fixed pairs: six extreme laws per triple, and
for each pair `a < b` the options "no constraint", "a above b", "b above a". -/
def pairsN (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    if a < b then [(a, b)] else []

def groupsExtremePairs (n : Nat) : List (Group (List Nat)) :=
  (triplesN n).map (fun t => lawsExtreme.map (holdsL t.1 t.2.1 t.2.2)) ++
  (pairsN n).map (fun ab => [fun _ => true, pairL ab.1 ab.2, pairL ab.2 ab.1])

/-! ### Locality and relabelling of laws -/

theorem neverL_filter (q : Nat → Bool) {x y z : Nat} (hx : q x = true) (hy : q y = true)
    (hz : q z = true) (p : Fin 3) (L : List Nat) :
    neverL x y z p (L.filter q) = neverL x y z p L := by
  simp only [neverL, before_filter q hx hy, before_filter q hx hz]

theorem neverL_map (f : Nat → Nat) (hf : Function.Injective f) (x y z : Nat) (p : Fin 3)
    (L : List Nat) : neverL (f x) (f y) (f z) p (L.map f) = neverL x y z p L := by
  simp only [neverL, before_map f hf]

theorem holdsL_filter (q : Nat → Bool) {a b c : Nat} (ha : q a = true) (hb : q b = true)
    (hc : q c = true) (law : Fin 3 × Fin 3) (L : List Nat) :
    holdsL a b c law (L.filter q) = holdsL a b c law L := by
  unfold holdsL
  split
  · exact neverL_filter q ha hb hc _ L
  · split
    · exact neverL_filter q hb ha hc _ L
    · exact neverL_filter q hc ha hb _ L

theorem pairL_filter (q : Nat → Bool) {a b : Nat} (ha : q a = true) (hb : q b = true)
    (L : List Nat) : pairL a b (L.filter q) = pairL a b L :=
  before_filter q ha hb L

end CDCert.ListOrder
