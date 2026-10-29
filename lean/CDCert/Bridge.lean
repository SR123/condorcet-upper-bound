/-
BUILD RECEIPT (Claude, 28 Oct 2026, 20:50 GMT): compiled independently against
Mathlib v4.26.0 built from source at the pinned commits (mathlib 2df2f01 and the
manifest's dependency revisions) and Codex's archived `Condorcet` modules; no
errors, no warnings; axiom audit in `receipts/bridge_axioms.txt`.
Differences from the candidate Codex compiled unchanged (archive of 20:40):
  * added "Generic solution sets": `lawOpt`, `pairOpt`, `lawOpt_toList`,
    `pairOpt_toList`, `allows_toList_iff`, `card_filter_eq_length`;
  * cosmetic only: shortened `never_iff_neverL`'s tactic tail, removed an unused
    simp argument in `map_val_finRange` and an unused binder in `isChoice_choiceOf`.
Exact imports: Condorcet.FullDomains, CDCert.ListOrders, CDCert.Four.
-/
/-
CDCert.Bridge — Codex's `Condorcet.Order (Fin n)` and the agreed finite base
`CDCert.Examples.orders n` (permutations of `List.range n`).

* `ofList` / `toList` and `orderEquiv : {L // L ∈ orders n} ≃ Condorcet.Order (Fin n)`;
  `toList` sorts `List.finRange n` from top to bottom.
* `before_toList`: the list comparison `before` is the order's comparison.
* `never_iff_neverL`, `holdsLaw_iff_holdsL`, `pairL_toList`: Codex's `Never`
  and `HoldsLaw`, and fixed pairs, are the list-level laws of `CDCert.ListOrders`.
* `mem_fullDomain_iff`, `card_fullDomain`, `fullDomain_enumerated`: every
  full domain `fullDomain sel` corresponds, member by member and with the same
  cardinality, to the list-level domain `domainOf (orders n) (choiceOf sel)`,
  which the verified enumerator lists for the groups `groupsFull n`.
* `f_four : f 4 = 9`: end-to-end check of the pipeline (semantic CD → maximal →
  full → bridge → kernel bitset check).

Depends on Codex's `Condorcet.FullDomains` (Mathlib v4.26.0) and on the Std-only
CDCert library.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import Condorcet.FullDomains
import CDCert.ListOrders
import CDCert.Four

namespace CDCert.Bridge

open Condorcet CDCert CDCert.Examples CDCert.ListOrder

/-! ### Lists to orders -/

/-- The order on `Fin n` read off a list of the agreed base. -/
def ofList {n : Nat} (L : List Nat) (hL : L ∈ orders n) : Condorcet.Order (Fin n) :=
  ⟨fun a b => before a.val b.val L,
    fun _ => before_self (nodup_of_mem_orders hL),
    fun _ _ _ hab hbc => before_trans (nodup_of_mem_orders hL) hab hbc,
    fun a b hab => before_total ((mem_of_mem_orders hL a).mpr a.isLt)
      ((mem_of_mem_orders hL b).mpr b.isLt) (fun h => hab (Fin.ext h))⟩

@[simp] theorem ofList_apply {n : Nat} (L : List Nat) (hL : L ∈ orders n) (a b : Fin n) :
    ofList L hL a b = before a.val b.val L := rfl

/-! ### Orders to lists -/

/-- `a` is above `b` or equal to it. -/
def weakAbove {n : Nat} (r : Condorcet.Order (Fin n)) (a b : Fin n) : Bool := !(r b a)

theorem weakAbove_trans {n : Nat} (r : Condorcet.Order (Fin n)) (a b c : Fin n)
    (hab : weakAbove r a b = true) (hbc : weakAbove r b c = true) :
    weakAbove r a c = true := by
  simp only [weakAbove, Bool.not_eq_true'] at hab hbc ⊢
  cases hca : r c a with
  | false => rfl
  | true =>
    by_cases h : a = b
    · subst h
      rw [hca] at hbc
      cases hbc
    · rcases r.total h with h' | h'
      · have := r.trans hca h'
        rw [this] at hbc
        cases hbc
      · rw [h'] at hab
        cases hab

theorem weakAbove_total {n : Nat} (r : Condorcet.Order (Fin n)) (a b : Fin n) :
    (weakAbove r a b || weakAbove r b a) = true := by
  unfold weakAbove
  cases hba : r b a with
  | false => rfl
  | true => rw [r.asymmetric hba]; rfl

/-- The list of an order: `Fin n` sorted from top to bottom, as naturals. -/
def toList {n : Nat} (r : Condorcet.Order (Fin n)) : List Nat :=
  ((List.finRange n).mergeSort (weakAbove r)).map Fin.val

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

theorem nodup_finRange' (n : Nat) : (List.finRange n).Nodup := by
  have h : ((List.finRange n).map Fin.val).Nodup := by
    rw [map_val_finRange]
    exact List.nodup_range
  exact h.of_map Fin.val

theorem toList_mem {n : Nat} (r : Condorcet.Order (Fin n)) : toList r ∈ orders n := by
  rw [mem_orders_iff, toList, ← map_val_finRange]
  exact (List.mergeSort_perm _ _).map Fin.val

/-- **The list comparison is the order's comparison.** -/
theorem before_toList {n : Nat} (r : Condorcet.Order (Fin n)) (a b : Fin n) :
    before a.val b.val (toList r) = r a b := by
  have hS := List.pairwise_mergeSort (weakAbove_trans r) (weakAbove_total r) (List.finRange n)
  have hperm := List.mergeSort_perm (List.finRange n) (weakAbove r)
  have hnd : ((List.finRange n).mergeSort (weakAbove r)).Nodup :=
    hperm.nodup_iff.mpr (nodup_finRange' n)
  have hmem : ∀ x : Fin n, x ∈ (List.finRange n).mergeSort (weakAbove r) :=
    fun x => hperm.mem_iff.mpr (List.mem_finRange x)
  rw [toList, before_map Fin.val Fin.val_injective]
  by_cases hab : a = b
  · subst hab
    rw [before_self hnd, r.irrefl]
  · cases h : r a b with
    | true =>
      rcases before_total (hmem a) (hmem b) hab with h1 | h1
      · exact h1
      · have h2 := rel_of_before hS h1
        simp [weakAbove, h] at h2
    | false =>
      cases h2 : before a b ((List.finRange n).mergeSort (weakAbove r)) with
      | false => rfl
      | true =>
        have h3 := rel_of_before hS h2
        simp only [weakAbove, Bool.not_eq_true'] at h3
        rcases r.total hab with h4 | h4
        · rw [h] at h4
          cases h4
        · rw [h3] at h4
          cases h4

theorem ofList_toList {n : Nat} (r : Condorcet.Order (Fin n)) : ofList (toList r) (toList_mem r) = r :=
  Condorcet.Order.ext (fun a b => before_toList r a b)

theorem toList_ofList {n : Nat} (L : List Nat) (hL : L ∈ orders n) :
    toList (ofList L hL) = L := by
  apply eq_of_before_eq (nodup_of_mem_orders (toList_mem _)) (nodup_of_mem_orders hL)
  · intro x
    rw [mem_of_mem_orders (toList_mem _), mem_of_mem_orders hL]
  · intro a b
    by_cases ha : a < n
    · by_cases hb : b < n
      · exact before_toList (ofList L hL) ⟨a, ha⟩ ⟨b, hb⟩
      · rw [before_eq_false_of_not_mem_right
            (fun h => hb ((mem_of_mem_orders (toList_mem _) b).mp h)),
          before_eq_false_of_not_mem_right (fun h => hb ((mem_of_mem_orders hL b).mp h))]
    · rw [before_eq_false_of_not_mem_left
          (fun h => ha ((mem_of_mem_orders (toList_mem _) a).mp h)),
        before_eq_false_of_not_mem_left (fun h => ha ((mem_of_mem_orders hL a).mp h))]

theorem toList_injective {n : Nat} : Function.Injective (toList (n := n)) := by
  intro r s h
  apply Condorcet.Order.ext
  intro a b
  rw [← before_toList r a b, ← before_toList s a b, h]

/-- **The agreed representation.** Orders on `Fin n` are exactly the lists in
`orders n`. -/
def orderEquiv (n : Nat) : {L : List Nat // L ∈ orders n} ≃ Condorcet.Order (Fin n) where
  toFun L := ofList L.1 L.2
  invFun r := ⟨toList r, toList_mem r⟩
  left_inv L := Subtype.ext (toList_ofList L.1 L.2)
  right_inv r := ofList_toList r

/-! ### Laws -/

theorem never_iff_neverL {n : Nat} (r : Condorcet.Order (Fin n)) (x y z : Fin n) (p : Fin 3) :
    Never r x y z p ↔ neverL x.val y.val z.val p (toList r) = true := by
  simp only [neverL, before_toList]
  fin_cases p <;> simp [Never]

theorem never_ofList_iff {n : Nat} (L : List Nat) (hL : L ∈ orders n) (x y z : Fin n)
    (p : Fin 3) : Never (ofList L hL) x y z p ↔ neverL x.val y.val z.val p L = true := by
  rw [never_iff_neverL, toList_ofList]

theorem holdsLaw_iff_holdsL {n : Nat} (r : Condorcet.Order (Fin n)) (t : Triple n) (law : Fin 3 × Fin 3) :
    HoldsLaw r t law ↔
      holdsL t.val.1.val t.val.2.1.val t.val.2.2.val law (toList r) = true := by
  unfold HoldsLaw holdsL
  by_cases h0 : law.1 = 0
  · rw [if_pos h0, if_pos h0]
    exact never_iff_neverL _ _ _ _ _
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : law.1 = 1
    · rw [if_pos h1, if_pos h1]
      exact never_iff_neverL _ _ _ _ _
    · rw [if_neg h1, if_neg h1]
      exact never_iff_neverL _ _ _ _ _

theorem pairL_toList {n : Nat} (r : Condorcet.Order (Fin n)) (a b : Fin n) :
    pairL a.val b.val (toList r) = r a b :=
  before_toList r a b

/-! ### Full domains -/

/-- The law a selection assigns to an increasing Nat triple (`(0,0)` elsewhere). -/
def selNat {n : Nat} (sel : Selection n) (t : Nat × Nat × Nat) : Fin 3 × Fin 3 :=
  if h : t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < n then
    sel ⟨(⟨t.1, by omega⟩, ⟨t.2.1, by omega⟩, ⟨t.2.2, h.2.2⟩), h.1, h.2.1⟩
  else (0, 0)

/-- The list-level choice of a selection: one law per increasing triple. -/
def choiceOf {n : Nat} (sel : Selection n) : List (Opt (List Nat)) :=
  (triplesN n).map fun t => holdsL t.1 t.2.1 t.2.2 (selNat sel t)

theorem isChoice_map_map {ι ω : Type} (f : ι → ω) (g : ι → List ω) :
    ∀ (l : List ι), (∀ i, i ∈ l → f i ∈ g i) → IsChoice (l.map f) (l.map g)
  | [], _ => IsChoice.nil
  | i :: l, h =>
    IsChoice.cons (h i List.mem_cons_self)
      (isChoice_map_map f g l (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem isChoice_choiceOf {n : Nat} (sel : Selection n) :
    IsChoice (choiceOf sel) (groupsFull n) :=
  isChoice_map_map _ _ _ (fun _ _ => List.mem_map_of_mem (mem_lawsAll _))

theorem selNat_triple {n : Nat} (sel : Selection n) (t : Triple n) :
    selNat sel (t.val.1.val, t.val.2.1.val, t.val.2.2.val) = sel t := by
  unfold selNat
  split
  · rfl
  · rename_i h
    exact absurd ⟨t.property.1, t.property.2, t.val.2.2.isLt⟩ h

/-- **Full domains correspond member by member.** -/
theorem mem_fullDomain_iff {n : Nat} (sel : Selection n) (r : Condorcet.Order (Fin n)) :
    r ∈ fullDomain sel ↔ toList r ∈ domainOf (orders n) (choiceOf sel) := by
  rw [mem_fullDomain, mem_domainOf]
  constructor
  · intro h
    refine ⟨toList_mem r, ?_⟩
    intro o ho
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
    obtain ⟨h1, h2, h3⟩ := mem_triplesN.mp ht
    let T : Triple n := ⟨(⟨t.1, by omega⟩, ⟨t.2.1, by omega⟩, ⟨t.2.2, h3⟩), h1, h2⟩
    have hsel : selNat sel t = sel T := by
      unfold selNat
      rw [dif_pos ⟨h1, h2, h3⟩]
    show holdsL t.1 t.2.1 t.2.2 (selNat sel t) (toList r) = true
    rw [hsel]
    exact (holdsLaw_iff_holdsL r T (sel T)).mp (h T)
  · rintro ⟨_, h⟩ t
    have ht : (t.val.1.val, t.val.2.1.val, t.val.2.2.val) ∈ triplesN n :=
      mem_triplesN.mpr ⟨t.property.1, t.property.2, t.val.2.2.isLt⟩
    have h' := h _ (List.mem_map_of_mem ht)
    simp only [selNat_triple] at h'
    exact (holdsLaw_iff_holdsL r t (sel t)).mpr h'

/-- **Same cardinality.** -/
theorem card_fullDomain {n : Nat} (sel : Selection n) :
    (fullDomain sel).card = (domainOf (orders n) (choiceOf sel)).length := by
  classical
  have hnd : (domainOf (orders n) (choiceOf sel)).Nodup := nodup_domainOf (orders_nodup n) _
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_bij (fun r _ => toList r)
  · intro r hr
    rw [List.mem_toFinset]
    exact (mem_fullDomain_iff sel r).mp hr
  · intro r₁ _ r₂ _ h
    exact toList_injective h
  · intro L hL
    rw [List.mem_toFinset] at hL
    have hLo : L ∈ orders n := (mem_domainOf.mp hL).1
    refine ⟨ofList L hLo, ?_, toList_ofList L hLo⟩
    rw [mem_fullDomain_iff, toList_ofList]
    exact hL

/-- **Coverage link.** The list-level image of every full domain is produced by
the verified enumerator for the groups `groupsFull n`. -/
theorem fullDomain_enumerated {n : Nat} (sel : Selection n) :
    domainOf (orders n) (choiceOf sel) ∈ enumerate (groupsFull n) (orders n) :=
  (mem_enumerate _ _ _).mpr ⟨_, isChoice_choiceOf sel, rfl⟩

/-! ### End-to-end check: `f 4 = 9` -/

/-- Fishburn's alternating scheme as a selection on `Fin 4`. -/
def fishSel : Selection 4 := fun t => CDCert.Four.fishLaw (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

theorem choiceOf_fishSel : choiceOf fishSel = CDCert.Four.fishChoice 4 := by
  unfold choiceOf CDCert.Four.fishChoice
  apply List.map_congr_left
  intro t ht
  obtain ⟨h1, h2, h3⟩ := mem_triplesN.mp ht
  unfold selNat
  rw [dif_pos ⟨h1, h2, h3⟩]
  rfl

theorem f_four : f 4 = 9 := by
  apply Nat.le_antisymm
  · obtain ⟨D, hD, hcard⟩ := exists_maximum_general 4
    obtain ⟨sel, rfl⟩ := (maximum_isMaximal hD hcard).isFull
    rw [← hcard, card_fullDomain]
    exact CDCert.Four.full4_card_le_nine _ (isChoice_choiceOf sel)
  · have h := card_le_f (fullDomain_isCondorcet fishSel)
    rwa [card_fullDomain, choiceOf_fishSel, CDCert.Four.fish4_length] at h

/-! ### Peak-pit: extreme selections give peak-pit full domains -/

/-- A common never condition at a fixed position on one of `a`, `b`, `c`. -/
def CommonLawAt {α : Type*} (D : Domain α) (a b c : α) (p : Fin 3) : Prop :=
  (∀ r ∈ D, Never r a b c p) ∨ (∀ r ∈ D, Never r b a c p) ∨ (∀ r ∈ D, Never r c a b p)

theorem CommonLawAt.swap12 {α : Type*} {D : Domain α} {a b c : α} {p : Fin 3}
    (H : CommonLawAt D a b c p) : CommonLawAt D b a c p := by
  rcases H with H | H | H
  · exact Or.inr (Or.inl H)
  · exact Or.inl H
  · exact Or.inr (Or.inr (fun r hr => (Never.swap r c a b p).mp (H r hr)))

theorem CommonLawAt.swap23 {α : Type*} {D : Domain α} {a b c : α} {p : Fin 3}
    (H : CommonLawAt D a b c p) : CommonLawAt D a c b p := by
  rcases H with H | H | H
  · exact Or.inl (fun r hr => (Never.swap r a b c p).mp (H r hr))
  · exact Or.inr (Or.inr H)
  · exact Or.inr (Or.inl H)

theorem sorted_extreme {n : Nat} {D : Domain (Fin n)}
    (H : ∀ a b c : Fin n, a < b → b < c → ∃ p : Fin 3, p ≠ 1 ∧ CommonLawAt D a b c p) :
    ExtremeRestricted D := by
  intro a b c hab hac hbc
  have key : ∃ p : Fin 3, p ≠ 1 ∧ CommonLawAt D a b c p := by
    rcases lt_or_gt_of_ne hab with hab | hba
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact H a b c hab hbc
      · rcases lt_or_gt_of_ne hac with hac | hca
        · obtain ⟨p, hp, h⟩ := H a c b hac hcb
          exact ⟨p, hp, h.swap23⟩
        · obtain ⟨p, hp, h⟩ := H c a b hca hab
          exact ⟨p, hp, h.swap12.swap23⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · obtain ⟨p, hp, h⟩ := H b a c hba hac
        exact ⟨p, hp, h.swap12⟩
      · rcases lt_or_gt_of_ne hbc with hbc | hcb
        · obtain ⟨p, hp, h⟩ := H b c a hbc hca
          exact ⟨p, hp, h.swap23.swap12⟩
        · obtain ⟨p, hp, h⟩ := H c b a hcb hba
          exact ⟨p, hp, h.swap12.swap23.swap12⟩
  exact key

/-- A full domain whose selected laws are all extreme is peak-pit. -/
theorem fullDomain_extremeRestricted {n : Nat} (sel : Selection n)
    (hsel : ∀ t, (sel t).2 ≠ 1) : ExtremeRestricted (fullDomain sel) := by
  apply sorted_extreme
  intro a b c hab hbc
  let t : Triple n := ⟨(a, b, c), hab, hbc⟩
  have H : ∀ r ∈ fullDomain sel, HoldsLaw r t (sel t) :=
    fun r hr => (mem_fullDomain sel r).mp hr t
  rcases hEq : sel t with ⟨x, p⟩
  have hp : p ≠ 1 := by
    have := hsel t
    rw [hEq] at this
    exact this
  rw [hEq] at H
  refine ⟨p, hp, ?_⟩
  fin_cases x
  · exact Or.inl H
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr H)

theorem fishSel_extreme : ∀ t, (fishSel t).2 ≠ 1 := by
  intro t
  unfold fishSel CDCert.Four.fishLaw
  split <;> decide

theorem h_four : h 4 = 9 := by
  apply Nat.le_antisymm
  · calc h 4 ≤ f 4 := h_le_f 4
      _ = 9 := f_four
  · have H := card_le_h (fullDomain_extremeRestricted fishSel fishSel_extreme).isPeakPit
    rwa [card_fullDomain, choiceOf_fishSel, CDCert.Four.fish4_length] at H

/-! ### Relabelling (support for C5) -/

/-- Apply a permutation of `Fin n` to a natural label (labels `≥ n` are fixed). -/
def relabelNat {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Nat) : Nat :=
  if h : x < n then (σ ⟨x, h⟩).val else x

theorem relabelNat_fin {n : Nat} (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    relabelNat σ a.val = (σ a).val := by
  unfold relabelNat
  rw [dif_pos a.isLt]

theorem relabelNat_injective {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (relabelNat σ) := by
  intro x y h
  unfold relabelNat at h
  by_cases hx : x < n <;> by_cases hy : y < n
  · rw [dif_pos hx, dif_pos hy] at h
    have := σ.injective (Fin.ext h)
    exact congrArg Fin.val this
  · rw [dif_pos hx, dif_neg hy] at h
    have := (σ ⟨x, hx⟩).isLt
    omega
  · rw [dif_neg hx, dif_pos hy] at h
    have := (σ ⟨y, hy⟩).isLt
    omega
  · rw [dif_neg hx, dif_neg hy] at h
    exact h

/-- **Relabelling at list level.** Restricting an order along a permutation `σ`
of the labels maps its list by `σ⁻¹`. -/
theorem toList_restrict_perm {n : Nat} (σ : Equiv.Perm (Fin n)) (r : Condorcet.Order (Fin n)) :
    toList (Condorcet.Order.restrict σ.toEmbedding r) = (toList r).map (relabelNat σ.symm) := by
  have hnd : (toList r).Nodup := nodup_of_mem_orders (toList_mem r)
  apply eq_of_before_eq (nodup_of_mem_orders (toList_mem _))
    (hnd.map (relabelNat_injective σ.symm))
  · intro x
    rw [mem_of_mem_orders (toList_mem _), List.mem_map]
    constructor
    · intro hx
      refine ⟨(σ ⟨x, hx⟩).val, (mem_of_mem_orders (toList_mem r) _).mpr (σ ⟨x, hx⟩).isLt, ?_⟩
      rw [relabelNat_fin σ.symm (σ ⟨x, hx⟩), Equiv.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      have hyn : y < n := (mem_of_mem_orders (toList_mem r) y).mp hy
      rw [show y = (⟨y, hyn⟩ : Fin n).val from rfl, relabelNat_fin]
      exact (σ.symm ⟨y, hyn⟩).isLt
  · intro a b
    by_cases ha : a < n
    · by_cases hb : b < n
      · have e1 : a = relabelNat σ.symm (σ ⟨a, ha⟩).val := by
          rw [relabelNat_fin, Equiv.symm_apply_apply]
        have e2 : b = relabelNat σ.symm (σ ⟨b, hb⟩).val := by
          rw [relabelNat_fin, Equiv.symm_apply_apply]
        rw [show before a b (toList (Condorcet.Order.restrict σ.toEmbedding r)) =
            (Condorcet.Order.restrict σ.toEmbedding r) ⟨a, ha⟩ ⟨b, hb⟩ from
            before_toList _ ⟨a, ha⟩ ⟨b, hb⟩]
        conv_rhs => rw [e1, e2]
        rw [before_map _ (relabelNat_injective σ.symm), before_toList]
        rfl
      · have hb' : b ∉ (toList r).map (relabelNat σ.symm) := by
          intro hm
          obtain ⟨y, hy, hyb⟩ := List.mem_map.mp hm
          have hyn : y < n := (mem_of_mem_orders (toList_mem r) y).mp hy
          rw [show y = (⟨y, hyn⟩ : Fin n).val from rfl, relabelNat_fin] at hyb
          exact hb (hyb ▸ (σ.symm ⟨y, hyn⟩).isLt)
        rw [before_eq_false_of_not_mem_right hb',
          before_eq_false_of_not_mem_right (fun h => hb ((mem_of_mem_orders (toList_mem _) b).mp h))]
    · have ha' : a ∉ (toList r).map (relabelNat σ.symm) := by
        intro hm
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp hm
        have hyn : y < n := (mem_of_mem_orders (toList_mem r) y).mp hy
        rw [show y = (⟨y, hyn⟩ : Fin n).val from rfl, relabelNat_fin] at hya
        exact ha (hya ▸ (σ.symm ⟨y, hyn⟩).isLt)
      rw [before_eq_false_of_not_mem_left ha',
        before_eq_false_of_not_mem_left (fun h => ha ((mem_of_mem_orders (toList_mem _) a).mp h))]

/-! ### Generic solution sets (for the extreme-law-plus-fixed-pair class) -/

/-- List option of a law on a triple of `Fin n`. -/
def lawOpt {n : Nat} (t : Triple n) (law : Fin 3 × Fin 3) : Opt (List Nat) :=
  holdsL t.val.1.val t.val.2.1.val t.val.2.2.val law

/-- List option of a fixed pair: coordinate `i = (a, c)`, `a < c`, has value `b`
(`b = true`: `a` above `c`), as in `Condorcet.encode`. -/
def pairOpt {n : Nat} (i : Pair n) (b : Bool) : Opt (List Nat) :=
  if b then pairL i.val.1.val i.val.2.val else pairL i.val.2.val i.val.1.val

theorem lawOpt_toList {n : Nat} (r : Condorcet.Order (Fin n)) (t : Triple n)
    (law : Fin 3 × Fin 3) : lawOpt t law (toList r) = true ↔ HoldsLaw r t law :=
  (holdsLaw_iff_holdsL r t law).symm

theorem pairOpt_toList {n : Nat} (r : Condorcet.Order (Fin n)) (i : Pair n) (b : Bool) :
    pairOpt i b (toList r) = true ↔ encode r i = b := by
  have hne : i.val.1 ≠ i.val.2 := ne_of_lt i.property
  unfold pairOpt encode
  cases b
  · rw [if_neg (by decide), pairL_toList, r.reverse_comparison hne]
    cases r i.val.1 i.val.2 <;> simp
  · rw [if_pos rfl, pairL_toList]

/-- **Laws and fixed pairs on `r` are `allows` on `toList r`.** -/
theorem allows_toList_iff {n : Nat} (laws : List (Triple n × (Fin 3 × Fin 3)))
    (pairs : List (Pair n × Bool)) (r : Condorcet.Order (Fin n)) :
    allows (laws.map (fun x => lawOpt x.1 x.2) ++ pairs.map (fun y => pairOpt y.1 y.2))
        (toList r) = true ↔
      (∀ x, x ∈ laws → HoldsLaw r x.1 x.2) ∧ (∀ y, y ∈ pairs → encode r y.1 = y.2) := by
  rw [allows_eq_true]
  constructor
  · intro h
    refine ⟨fun x hx => (lawOpt_toList r x.1 x.2).mp
        (h _ (List.mem_append_left _ (List.mem_map_of_mem hx))),
      fun y hy => (pairOpt_toList r y.1 y.2).mp
        (h _ (List.mem_append_right _ (List.mem_map_of_mem hy)))⟩
  · rintro ⟨h1, h2⟩ o ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
      exact (lawOpt_toList r x.1 x.2).mpr (h1 x hx)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
      exact (pairOpt_toList r y.1 y.2).mpr (h2 y hy)

/-- **Generic cardinality transfer.** A finset of orders cut out by a predicate
that matches `allows opts` on lists has the size of `domainOf (orders n) opts`. -/
theorem card_filter_eq_length {n : Nat} (P : Condorcet.Order (Fin n) → Prop) [DecidablePred P]
    (opts : List (Opt (List Nat))) (hP : ∀ r, P r ↔ allows opts (toList r) = true) :
    (Finset.univ.filter P).card = (domainOf (orders n) opts).length := by
  classical
  have hnd : (domainOf (orders n) opts).Nodup := nodup_domainOf (orders_nodup n) _
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_bij (fun r _ => toList r)
  · intro r hr
    rw [List.mem_toFinset, mem_domainOf]
    rw [Finset.mem_filter] at hr
    exact ⟨toList_mem r, allows_eq_true.mp ((hP r).mp hr.2)⟩
  · intro r₁ _ r₂ _ h
    exact toList_injective h
  · intro L hL
    rw [List.mem_toFinset, mem_domainOf] at hL
    refine ⟨ofList L hL.1, ?_, toList_ofList L hL.1⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (hP _).mpr ?_⟩
    rw [toList_ofList]
    exact allows_eq_true.mpr hL.2

end CDCert.Bridge
