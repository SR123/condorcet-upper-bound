/-
CDCert.Extension — obligation C2: restricting *defining conditions*.

Groups for "extreme laws plus fixed pairs" are built label by label:
`groupsEP (k+1) = groupsEP k ++ groupsNew k`, where `groupsNew k` has the six
extreme laws on every triple `(a, b, k)` with `a < b < k` and the options
{none, a above k, k above a} on every pair `(a, k)`. (For `k = 5`: ten new
triples and five new pairs, as in the paper's six-generator.)

* `local_groupsEP`: every option of `groupsEP k` depends only on the
  restriction of an order to the labels `< k`;
* `extension_eq` (C2): for choices `cOld` (old groups) and `cNew`,
  `domainOf (orders (k+1)) (cOld ++ cNew)
     = domainOf (extBase k (domainOf (orders k) cOld)) cNew`,
  an equality of lists, where `extBase k R` is the orders on `k+1` labels whose
  restriction lies in `R`;
* `isChoice_groupsEP_succ`: choices for `groupsEP (k+1)` are exactly old
  choices followed by new choices.

So every domain defined over `k+1` labels is the extension, by the new
conditions, of the solution set of its own restricted conditions — not of its
projection — as the paper states.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.ListOrders

namespace CDCert.ListOrder

open CDCert CDCert.Examples

/-! ### Label-by-label groups -/

/-- New triples `(a, b, k)` with `a < b < k`. -/
def newTriples (k : Nat) : List (Nat × Nat × Nat) :=
  (List.range k).flatMap fun a => (List.range k).flatMap fun b =>
    if a < b then [(a, b, k)] else []

/-- Options for a fixed pair: none, `a` above `b`, `b` above `a`. -/
def pairOptions (a b : Nat) : Group (List Nat) := [fun _ => true, pairL a b, pairL b a]

/-- Groups introduced with label `k`. -/
def groupsNew (k : Nat) : List (Group (List Nat)) :=
  (newTriples k).map (fun t => lawsExtreme.map (holdsL t.1 t.2.1 t.2.2)) ++
  (List.range k).map (fun a => pairOptions a k)

/-- Groups for extreme laws plus fixed pairs on labels `< k`, built label by label. -/
def groupsEP : Nat → List (Group (List Nat))
  | 0 => []
  | k + 1 => groupsEP k ++ groupsNew k

theorem mem_newTriples {k : Nat} {t : Nat × Nat × Nat} :
    t ∈ newTriples k ↔ t.1 < t.2.1 ∧ t.2.1 < k ∧ t.2.2 = k := by
  obtain ⟨a, b, c⟩ := t
  simp only [newTriples, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a', ha, b', hb, h⟩
    split at h
    · rename_i hlt
      rw [List.mem_singleton] at h
      cases h
      exact ⟨hlt, hb, rfl⟩
    · cases h
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨a, by omega, b, h2, ?_⟩
    rw [if_pos h1]
    exact List.mem_singleton_self _

/-! ### Locality -/

/-- Delete the labels `≥ k`. -/
def restrictTo (k : Nat) (L : List Nat) : List Nat := L.filter (fun a => decide (a < k))

/-- An option depends only on the labels `< k`. -/
def Local (k : Nat) (o : Opt (List Nat)) : Prop := ∀ L, o (restrictTo k L) = o L

theorem local_holdsL {k a b c : Nat} (ha : a < k) (hb : b < k) (hc : c < k)
    (law : Fin 3 × Fin 3) : Local k (holdsL a b c law) := fun L =>
  holdsL_filter _ (decide_eq_true ha) (decide_eq_true hb) (decide_eq_true hc) law L

theorem local_pairL {k a b : Nat} (ha : a < k) (hb : b < k) : Local k (pairL a b) := fun L =>
  pairL_filter _ (decide_eq_true ha) (decide_eq_true hb) L

theorem local_mono {k k' : Nat} (hk : k ≤ k') {o : Opt (List Nat)} (h : Local k o) :
    Local k' o := by
  intro L
  have h1 : restrictTo k (restrictTo k' L) = restrictTo k L := by
    unfold restrictTo
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases hx : x < k
    · simp [hx, Nat.lt_of_lt_of_le hx hk]
    · simp [hx]
  rw [← h (restrictTo k' L), h1, h L]

theorem local_groupsNew (k : Nat) :
    ∀ g, g ∈ groupsNew k → ∀ o, o ∈ g → Local (k + 1) o := by
  intro g hg o ho
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2, h3⟩ := mem_newTriples.mp ht
    obtain ⟨law, _, rfl⟩ := List.mem_map.mp ho
    exact local_holdsL (by omega) (by omega) (by omega) law
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at ha
    simp only [pairOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · intro L
      rfl
    · exact local_pairL (by omega) (by omega)
    · exact local_pairL (by omega) (by omega)

theorem local_groupsEP : ∀ (k : Nat), ∀ g, g ∈ groupsEP k → ∀ o, o ∈ g → Local k o
  | 0 => by intro g hg; cases hg
  | k + 1 => by
    intro g hg o ho
    rcases List.mem_append.mp hg with hg | hg
    · exact local_mono (Nat.le_succ k) (local_groupsEP k g hg o ho)
    · exact local_groupsNew k g hg o ho

theorem isChoice_local {k : Nat} {gs : List (Group (List Nat))}
    (hgs : ∀ g, g ∈ gs → ∀ o, o ∈ g → Local k o) {c : List (Opt (List Nat))}
    (hc : IsChoice c gs) : ∀ o, o ∈ c → Local k o := by
  intro o ho
  obtain ⟨g, hg, hog⟩ := hc.exists_group o ho
  exact hgs g hg o hog

theorem allows_restrictTo {k : Nat} {c : List (Opt (List Nat))} (hc : ∀ o, o ∈ c → Local k o)
    (L : List Nat) : allows c (restrictTo k L) = allows c L := by
  unfold allows
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h o ho
    rw [← hc o ho L]
    exact h o ho
  · intro h o ho
    rw [hc o ho L]
    exact h o ho

/-! ### Restriction of orders -/

theorem range_filter_lt (k : Nat) :
    (List.range (k + 1)).filter (fun a => decide (a < k)) = List.range k := by
  rw [List.range_succ, List.filter_append]
  have h1 : (List.range k).filter (fun a => decide (a < k)) = List.range k := by
    rw [List.filter_eq_self]
    intro a ha
    simpa using ha
  rw [h1]
  simp

theorem restrictTo_mem_orders {k : Nat} {L : List Nat} (h : L ∈ orders (k + 1)) :
    restrictTo k L ∈ orders k := by
  rw [mem_orders_iff] at h ⊢
  unfold restrictTo
  rw [← range_filter_lt k]
  exact h.filter _

/-- Orders on `k+1` labels whose restriction lies in `R`. -/
def extBase (k : Nat) (R : List (List Nat)) : List (List Nat) :=
  (orders (k + 1)).filter (fun L => decide (restrictTo k L ∈ R))

/-! ### C2 -/

/-- **C2 (restriction of defining conditions).** -/
theorem extension_eq {k : Nat} {cOld cNew : List (Opt (List Nat))}
    (hloc : ∀ o, o ∈ cOld → Local k o) :
    domainOf (orders (k + 1)) (cOld ++ cNew) =
      domainOf (extBase k (domainOf (orders k) cOld)) cNew := by
  unfold domainOf restrict extBase
  rw [List.filter_filter]
  apply List.filter_congr
  intro L hL
  have hmem : decide (restrictTo k L ∈ (orders k).filter (allows cOld)) = allows cOld L := by
    rw [← allows_restrictTo hloc L]
    cases h : allows cOld (restrictTo k L)
    · apply decide_eq_false
      intro hm
      rw [List.mem_filter, h] at hm
      cases hm.2
    · apply decide_eq_true
      exact List.mem_filter.mpr ⟨restrictTo_mem_orders hL, h⟩
  rw [hmem]
  unfold allows
  rw [List.all_append, Bool.and_comm]

theorem isChoice_append {ω : Type} :
    ∀ {c : List ω} {gs₁ gs₂ : List (List ω)},
      IsChoice c (gs₁ ++ gs₂) ↔
        ∃ c₁ c₂, c = c₁ ++ c₂ ∧ IsChoice c₁ gs₁ ∧ IsChoice c₂ gs₂
  | c, [], gs₂ => by
    simp only [List.nil_append]
    constructor
    · intro h
      exact ⟨[], c, rfl, IsChoice.nil, h⟩
    · rintro ⟨c₁, c₂, rfl, h₁, h₂⟩
      rw [isChoice_nil_iff] at h₁
      subst h₁
      exact h₂
  | c, g :: gs₁, gs₂ => by
    rw [List.cons_append, isChoice_cons_iff]
    constructor
    · rintro ⟨o, ho, os, hos, rfl⟩
      obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := isChoice_append.mp hos
      exact ⟨o :: c₁, c₂, rfl, IsChoice.cons ho h₁, h₂⟩
    · rintro ⟨c₁, c₂, rfl, h₁, h₂⟩
      obtain ⟨o, ho, os, hos, rfl⟩ := isChoice_cons_iff.mp h₁
      exact ⟨o, ho, os ++ c₂, isChoice_append.mpr ⟨os, c₂, rfl, hos, h₂⟩, rfl⟩

/-- Choices for `groupsEP (k+1)` are old choices followed by new choices. -/
theorem isChoice_groupsEP_succ {k : Nat} {c : List (Opt (List Nat))} :
    IsChoice c (groupsEP (k + 1)) ↔
      ∃ cOld cNew, c = cOld ++ cNew ∧ IsChoice cOld (groupsEP k) ∧ IsChoice cNew (groupsNew k) :=
  isChoice_append

/-- **Every domain over `k+1` labels is the extension of the solution set of
its restricted conditions.** -/
theorem domain_succ_eq_extension {k : Nat} {c : List (Opt (List Nat))}
    (hc : IsChoice c (groupsEP (k + 1))) :
    ∃ cOld cNew, IsChoice cOld (groupsEP k) ∧ IsChoice cNew (groupsNew k) ∧
      domainOf (orders (k + 1)) c = domainOf (extBase k (domainOf (orders k) cOld)) cNew := by
  obtain ⟨cOld, cNew, rfl, hOld, hNew⟩ := isChoice_groupsEP_succ.mp hc
  exact ⟨cOld, cNew, hOld, hNew, extension_eq (isChoice_local (local_groupsEP k) hOld)⟩

end CDCert.ListOrder
