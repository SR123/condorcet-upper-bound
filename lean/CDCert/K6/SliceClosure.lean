/-
CDCert.K6.SliceClosure — **slices of `groupsEP (k+1)` domains are `groupsEP k`
domains or empty** (the paper's "every nonempty slice belongs to `𝓕_{k-1}`").

Domains are predicates on orders. `botP x H` (resp. `topP y H`) is the bottom
(top) slice: the orders `L` of `0..k-1` with `L.map (up x) ++ [x]` (resp.
`y :: L.map (up y)`) in `H`.

* `slice_bot_last`, `slice_top_last`: slices at the last label `k`. The laws on the
  new triples `(a, b, k)` become fixed pairs (or kill the slice), the fixed pairs
  `(a, k)` become trivial (or kill it); conflicting fixed pairs give the empty slice.
* `isDom_relabel`: domains are closed under relabelling;
* `botP_relabel`, `topP_relabel`: slices of a relabelled domain are relabelled slices;
* `slice_bot`, `slice_top`: slices at every label.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Relabel

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-- `p` is the solution set (on orders of `0..k-1`) of a choice for `groupsEP k`. -/
def IsDom (k : Nat) (p : List Nat → Bool) : Prop :=
  ∃ c, IsChoice c (groupsEP k) ∧ ∀ L, L ∈ orders k → p L = allows c L

/-- `p` is empty on the orders of `0..k-1`. -/
def IsEmptyOn (k : Nat) (p : List Nat → Bool) : Prop := ∀ L, L ∈ orders k → p L = false

/-- Bottom slice at `x`. -/
def botP (x : Nat) (H : List Nat → Bool) : List Nat → Bool := fun L => H (L.map (up x) ++ [x])

/-- Top slice at `y`. -/
def topP (y : Nat) (H : List Nat → Bool) : List Nat → Bool := fun L => H (y :: L.map (up y))

/-! ### `before` at the ends -/

theorem before_append_last_left {k a : Nat} : ∀ {L : List Nat}, a ∈ L → k ∉ L →
    before a k (L ++ [k]) = true
  | y :: ys, ha, hk => by
    rw [List.cons_append, before_cons]
    by_cases hya : y = a
    · rw [if_pos hya]; simp
    · rw [if_neg hya]
      have hyk : y ≠ k := fun h => hk (h ▸ List.mem_cons_self)
      rw [if_neg hyk]
      exact before_append_last_left ((List.mem_cons.mp ha).resolve_left (fun h => hya h.symm))
        (fun h => hk (List.mem_cons_of_mem _ h))

theorem before_append_last_right {k a : Nat} (hak : a ≠ k) : ∀ {L : List Nat}, k ∉ L →
    before k a (L ++ [k]) = false
  | [], _ => by
    show before k a [k] = false
    rw [before_cons, if_pos rfl]
    simp
  | y :: ys, hk => by
    rw [List.cons_append, before_cons]
    have hyk : y ≠ k := fun h => hk (h ▸ List.mem_cons_self)
    rw [if_neg hyk]
    by_cases hya : y = a
    · rw [if_pos hya]
    · rw [if_neg hya]
      exact before_append_last_right hak (fun h => hk (List.mem_cons_of_mem _ h))

theorem before_append_last {k a b : Nat} (hak : a ≠ k) (hbk : b ≠ k) {L : List Nat} (hk : k ∉ L) :
    before a b (L ++ [k]) = before a b L := by
  have h1 : (L ++ [k]).filter (fun z => z != k) = L := by
    rw [List.filter_append]
    have : L.filter (fun z => z != k) = L := by
      rw [List.filter_eq_self]
      intro z hz
      have : z ≠ k := fun h => hk (h ▸ hz)
      simpa using this
    rw [this]
    simp
  rw [← before_filter (fun z => z != k) (by simpa using hak) (by simpa using hbk), h1]

theorem before_cons_first_left {k a : Nat} {L : List Nat} (ha : a ∈ L) : before k a (k :: L) = true := by
  rw [before_cons, if_pos rfl]; simpa using ha

theorem before_cons_first_right {k a : Nat} (hak : a ≠ k) (L : List Nat) : before a k (k :: L) = false := by
  rw [before_cons, if_neg (fun h => hak h.symm), if_pos rfl]

theorem before_cons_first {k a b : Nat} (hak : a ≠ k) (hbk : b ≠ k) (L : List Nat) :
    before a b (k :: L) = before a b L := by
  rw [before_cons, if_neg (fun h => hak h.symm), if_neg (fun h => hbk h.symm)]

/-! ### Induced fixed pairs -/

/-- Fixed pair induced on `(a, b)` by the law on `(a, b, k)` when `k` is last. -/
def indB (law : Fin 3 × Fin 3) : Option Bool :=
  if law = (0, 0) then some false else if law = (1, 0) then some true else none

/-- Fixed pair induced on `(a, b)` by the law on `(a, b, k)` when `k` is first. -/
def indT (law : Fin 3 × Fin 3) : Option Bool :=
  if law = (0, 2) then some true else if law = (1, 2) then some false else none

/-- First nontrivial comparison. -/
def mergeO (u v : Option Bool) : Option Bool :=
  match u with
  | none => v
  | some x => some x

/-- Two comparisons that cannot hold together. -/
def conflictO (u v : Option Bool) : Bool :=
  match u, v with
  | some x, some y => x != y
  | _, _ => false

theorem pairChoice_merge {a b : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L)
    (hab : a ≠ b) {u v : Option Bool} (h : conflictO u v = false) :
    pairChoice a b (mergeO u v) L = (pairChoice a b u L && pairChoice a b v L) := by
  cases u with
  | none => simp [mergeO, pairChoice]
  | some x =>
    cases v with
    | none => simp [mergeO, pairChoice]
    | some y =>
      have hxy : x = y := by
        simp only [conflictO, bne_eq_false_iff_eq] at h
        exact h
      subst hxy
      simp [mergeO]

theorem pairChoice_conflict {a b : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L)
    (hab : a ≠ b) {u v : Option Bool} (h : conflictO u v = true) :
    (pairChoice a b u L && pairChoice a b v L) = false := by
  cases u with
  | none => simp [conflictO] at h
  | some x =>
    cases v with
    | none => simp [conflictO] at h
    | some y =>
      have hxy : x ≠ y := by simpa [conflictO] using h
      have hne := before_eq_not hnd ha hb hab
      cases x <;> cases y
      · exact absurd rfl hxy
      · show (before b a L && before a b L) = false
        rw [hne]; cases before b a L <;> rfl
      · show (before a b L && before b a L) = false
        rw [hne]; cases before b a L <;> rfl
      · exact absurd rfl hxy

/-! ### Laws with the new label at an end -/

theorem holdsL_append_last {k a b : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L)
    (hk : k ∉ L) (hab : a ≠ b) {law : Fin 3 × Fin 3} (hlaw : law ∈ lawsExtreme) :
    holdsL a b k law (L ++ [k]) = (if law = (2, 2) then false else pairChoice a b (indB law) L) := by
  have hak : a ≠ k := fun h => hk (h ▸ ha)
  have hbk : b ≠ k := fun h => hk (h ▸ hb)
  have e1 := before_append_last_left (k := k) ha hk
  have e2 := before_append_last_left (k := k) hb hk
  have e3 := before_append_last_right (k := k) hak hk
  have e4 := before_append_last_right (k := k) hbk hk
  have e5 := before_append_last hak hbk hk
  have e6 := before_append_last hbk hak hk
  have hne := before_eq_not hnd ha hb hab
  simp only [lawsExtreme, List.mem_cons, List.not_mem_nil, or_false] at hlaw
  rcases hlaw with rfl | rfl | rfl | rfl | rfl | rfl
  · show neverL a b k 0 (L ++ [k]) = pairChoice a b (some false) L
    simp only [neverL, if_true, e1, e5, Bool.and_true, pairChoice, pairL, hne, Bool.not_not]
  · show neverL a b k 2 (L ++ [k]) = pairChoice a b none L
    simp [neverL, e1, pairChoice]
  · show neverL b a k 0 (L ++ [k]) = pairChoice a b (some true) L
    simp only [neverL, if_true, e2, e6, Bool.and_true, pairChoice, pairL, hne]
  · show neverL b a k 2 (L ++ [k]) = pairChoice a b none L
    simp [neverL, e2, pairChoice]
  · show neverL k a b 0 (L ++ [k]) = pairChoice a b none L
    simp [neverL, e3, pairChoice]
  · show neverL k a b 2 (L ++ [k]) = false
    simp [neverL, e3, e4]

theorem holdsL_cons_first {k a b : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) (hb : b ∈ L)
    (hk : k ∉ L) (hab : a ≠ b) {law : Fin 3 × Fin 3} (hlaw : law ∈ lawsExtreme) :
    holdsL a b k law (k :: L) = (if law = (2, 0) then false else pairChoice a b (indT law) L) := by
  have hak : a ≠ k := fun h => hk (h ▸ ha)
  have hbk : b ≠ k := fun h => hk (h ▸ hb)
  have e1 := before_cons_first_left (k := k) ha
  have e2 := before_cons_first_left (k := k) hb
  have e3 := before_cons_first_right hak L
  have e4 := before_cons_first_right hbk L
  have e5 := before_cons_first hak hbk L
  have e6 := before_cons_first hbk hak L
  have hne := before_eq_not hnd ha hb hab
  simp only [lawsExtreme, List.mem_cons, List.not_mem_nil, or_false] at hlaw
  rcases hlaw with rfl | rfl | rfl | rfl | rfl | rfl
  · show neverL a b k 0 (k :: L) = pairChoice a b none L
    simp [neverL, e3, pairChoice]
  · show neverL a b k 2 (k :: L) = pairChoice a b (some true) L
    simp [neverL, e3, e5, pairChoice, pairL]
  · show neverL b a k 0 (k :: L) = pairChoice a b none L
    simp [neverL, e4, pairChoice]
  · show neverL b a k 2 (k :: L) = pairChoice a b (some false) L
    simp [neverL, e4, e6, pairChoice, pairL]
  · show neverL k a b 0 (k :: L) = false
    simp [neverL, e1, e2]
  · show neverL k a b 2 (k :: L) = pairChoice a b none L
    simp [neverL, e1, pairChoice]

/-! ### Slices at the last label -/

theorem map_up_last {k : Nat} {L : List Nat} (hL : L ∈ orders k) : L.map (up k) = L := by
  conv => rhs; rw [← List.map_id L]
  apply List.map_congr_left
  intro a ha
  have := (mem_of_mem_orders hL a).mp ha
  unfold up
  rw [if_pos this]
  rfl

theorem append_last_mem_orders {k : Nat} {L : List Nat} (hL : L ∈ orders k) : L ++ [k] ∈ orders (k + 1) := by
  rw [mem_orders_iff] at hL ⊢
  rw [List.range_succ]
  exact hL.append_right [k]

theorem cons_first_mem_orders {k : Nat} {L : List Nat} (hL : L ∈ orders k) : k :: L ∈ orders (k + 1) := by
  rw [mem_orders_iff] at hL ⊢
  rw [List.range_succ]
  exact (List.perm_append_singleton k L).symm.trans (hL.append_right [k])

theorem restrictTo_append_last {k : Nat} {L : List Nat} (hL : L ∈ orders k) : restrictTo k (L ++ [k]) = L := by
  unfold restrictTo
  rw [List.filter_append, List.filter_eq_self.mpr]
  · simp
  · intro a ha
    simpa using (mem_of_mem_orders hL a).mp ha

theorem restrictTo_cons_first {k : Nat} {L : List Nat} (hL : L ∈ orders k) : restrictTo k (k :: L) = L := by
  unfold restrictTo
  rw [List.filter_cons, if_neg (by simp), List.filter_eq_self.mpr]
  intro a ha
  simpa using (mem_of_mem_orders hL a).mp ha

theorem not_mem_self_orders {k : Nat} {L : List Nat} (hL : L ∈ orders k) : k ∉ L := fun h => by
  have := (mem_of_mem_orders hL k).mp h
  omega

/-- **Bottom slice at the last label.** -/
theorem slice_bot_last (k : Nat) {H : List Nat → Bool} (hH : IsDom (k + 1) H) :
    IsDom k (botP k H) ∨ IsEmptyOn k (botP k H) := by
  obtain ⟨c, hc, hHc⟩ := hH
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff (k + 1) c hc
  have hOld : IsChoice (choiceEPN lawN pairN k) (groupsEP k) :=
    isChoice_choiceEPN lawN pairN k (fun _ t _ _ => hlaw t)
  have key : ∀ L, L ∈ orders k → botP k H L =
      (allows (choiceEPN lawN pairN k) L && allows (choiceNew lawN pairN k) (L ++ [k])) := by
    intro L hL
    unfold botP
    rw [map_up_last hL, hHc _ (append_last_mem_orders hL)]
    show allows (choiceEPN lawN pairN k ++ choiceNew lawN pairN k) (L ++ [k]) = _
    rw [allows_append, (allows_restrictTo (isChoice_local (local_groupsEP k) hOld) (L ++ [k])).symm,
      restrictTo_append_last hL]
  -- the new triple and pair options on `L ++ [k]`
  have htrip : ∀ L, L ∈ orders k → ∀ a b, a < b → b < k →
      holdsL a b k (lawN (a, b, k)) (L ++ [k]) =
        (if lawN (a, b, k) = (2, 2) then false else pairChoice a b (indB (lawN (a, b, k))) L) := by
    intro L hL a b hab hb
    exact holdsL_append_last (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
      ((mem_of_mem_orders hL b).mpr hb) (not_mem_self_orders hL) (by omega) (hlaw _)
  have hpair : ∀ L, L ∈ orders k → ∀ a, a < k →
      pairChoice a k (pairN a k) (L ++ [k]) = (pairN a k != some false) := by
    intro L hL a ha
    have hk := not_mem_self_orders hL
    have haL : a ∈ L := (mem_of_mem_orders hL a).mpr ha
    cases h : pairN a k with
    | none => rfl
    | some v =>
      cases v
      · show before k a (L ++ [k]) = _
        rw [before_append_last_right (by omega) hk]; rfl
      · show before a k (L ++ [k]) = _
        rw [before_append_last_left haL hk]; rfl
  have hnew : ∀ L, L ∈ orders k → (allows (choiceNew lawN pairN k) (L ++ [k]) = true ↔
      (∀ a b, a < b → b < k →
        (if lawN (a, b, k) = (2, 2) then false else pairChoice a b (indB (lawN (a, b, k))) L) = true) ∧
      (∀ a, a < k → (pairN a k != some false) = true)) := by
    intro L hL
    rw [allows_choiceNew]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a b hab hb => ?_, fun a ha => ?_⟩
      · have := h1 (a, b, k) (mem_newTriples.mpr ⟨hab, hb, rfl⟩)
        rw [htrip L hL a b hab hb] at this
        exact this
      · rw [← hpair L hL a ha]; exact h2 a ha
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, fun a ha => ?_⟩
      · obtain ⟨t1, t2, t3⟩ := mem_newTriples.mp ht
        obtain ⟨a, b, c⟩ := t
        simp only at t1 t2 t3
        subst t3
        rw [htrip L hL a b t1 t2]
        exact h1 a b t1 t2
      · rw [hpair L hL a ha]; exact h2 a ha
  by_cases hkill : (∃ a b, a < b ∧ b < k ∧ lawN (a, b, k) = (2, 2)) ∨ (∃ a, a < k ∧ pairN a k = some false)
  · right
    intro L hL
    rw [key L hL]
    have : allows (choiceNew lawN pairN k) (L ++ [k]) = false := by
      cases h : allows (choiceNew lawN pairN k) (L ++ [k])
      · rfl
      · obtain ⟨h1, h2⟩ := (hnew L hL).mp h
        rcases hkill with ⟨a, b, hab, hb, hl⟩ | ⟨a, ha, hp⟩
        · have := h1 a b hab hb
          rw [if_pos hl] at this
          cases this
        · have := h2 a ha
          rw [hp] at this
          cases this
    rw [this, Bool.and_false]
  · have hk1 : ∀ a b, a < b → b < k → lawN (a, b, k) ≠ (2, 2) := fun a b hab hb h =>
      hkill (Or.inl ⟨a, b, hab, hb, h⟩)
    have hk2 : ∀ a, a < k → pairN a k ≠ some false := fun a ha h => hkill (Or.inr ⟨a, ha, h⟩)
    by_cases hconf : ∃ a b, a < b ∧ b < k ∧ conflictO (pairN a b) (indB (lawN (a, b, k))) = true
    · right
      intro L hL
      rw [key L hL]
      obtain ⟨a, b, hab, hb, hcf⟩ := hconf
      cases h1 : allows (choiceEPN lawN pairN k) L
      · rfl
      · cases h2 : allows (choiceNew lawN pairN k) (L ++ [k])
        · rfl
        · exfalso
          have hp1 := ((allows_choiceEPN lawN pairN L k).mp h1).2 a b hab hb
          have hp2 := ((hnew L hL).mp h2).1 a b hab hb
          rw [if_neg (hk1 a b hab hb)] at hp2
          have := pairChoice_conflict (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
            ((mem_of_mem_orders hL b).mpr hb) (by omega) hcf
          rw [hp1, hp2] at this
          cases this
    · left
      have hnc : ∀ a b, a < b → b < k → conflictO (pairN a b) (indB (lawN (a, b, k))) = false := by
        intro a b hab hb
        cases h : conflictO (pairN a b) (indB (lawN (a, b, k)))
        · rfl
        · exact absurd ⟨a, b, hab, hb, h⟩ hconf
      refine ⟨choiceEPN lawN (fun a b => if b < k then mergeO (pairN a b) (indB (lawN (a, b, k)))
        else pairN a b) k, isChoice_choiceEPN _ _ k (fun _ t _ _ => hlaw t), ?_⟩
      intro L hL
      rw [key L hL]
      apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true, allows_choiceEPN, allows_choiceEPN, hnew L hL]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, _⟩
        refine ⟨h1, fun a b hab hb => ?_⟩
        simp only [if_pos hb]
        rw [pairChoice_merge (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
          ((mem_of_mem_orders hL b).mpr hb) (by omega) (hnc a b hab hb), h2 a b hab hb, Bool.true_and]
        have := h3 a b hab hb
        rw [if_neg (hk1 a b hab hb)] at this
        exact this
      · rintro ⟨h1, h2⟩
        have hm : ∀ a b, a < b → b < k → pairChoice a b (pairN a b) L = true ∧
            pairChoice a b (indB (lawN (a, b, k))) L = true := by
          intro a b hab hb
          have := h2 a b hab hb
          simp only [if_pos hb] at this
          rw [pairChoice_merge (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
            ((mem_of_mem_orders hL b).mpr hb) (by omega) (hnc a b hab hb), Bool.and_eq_true] at this
          exact this
        refine ⟨⟨h1, fun a b hab hb => (hm a b hab hb).1⟩, fun a b hab hb => ?_, fun a ha => ?_⟩
        · rw [if_neg (hk1 a b hab hb)]; exact (hm a b hab hb).2
        · cases h : pairN a k with
          | none => rfl
          | some v => cases v
                      · exact absurd h (hk2 a ha)
                      · rfl

/-- **Top slice at the last label.** -/
theorem slice_top_last (k : Nat) {H : List Nat → Bool} (hH : IsDom (k + 1) H) :
    IsDom k (topP k H) ∨ IsEmptyOn k (topP k H) := by
  obtain ⟨c, hc, hHc⟩ := hH
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff (k + 1) c hc
  have hOld : IsChoice (choiceEPN lawN pairN k) (groupsEP k) :=
    isChoice_choiceEPN lawN pairN k (fun _ t _ _ => hlaw t)
  have key : ∀ L, L ∈ orders k → topP k H L =
      (allows (choiceEPN lawN pairN k) L && allows (choiceNew lawN pairN k) (k :: L)) := by
    intro L hL
    unfold topP
    rw [map_up_last hL, hHc _ (cons_first_mem_orders hL)]
    show allows (choiceEPN lawN pairN k ++ choiceNew lawN pairN k) (k :: L) = _
    rw [allows_append, (allows_restrictTo (isChoice_local (local_groupsEP k) hOld) (k :: L)).symm,
      restrictTo_cons_first hL]
  have htrip : ∀ L, L ∈ orders k → ∀ a b, a < b → b < k →
      holdsL a b k (lawN (a, b, k)) (k :: L) =
        (if lawN (a, b, k) = (2, 0) then false else pairChoice a b (indT (lawN (a, b, k))) L) := by
    intro L hL a b hab hb
    exact holdsL_cons_first (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
      ((mem_of_mem_orders hL b).mpr hb) (not_mem_self_orders hL) (by omega) (hlaw _)
  have hpair : ∀ L, L ∈ orders k → ∀ a, a < k →
      pairChoice a k (pairN a k) (k :: L) = (pairN a k != some true) := by
    intro L hL a ha
    have haL : a ∈ L := (mem_of_mem_orders hL a).mpr ha
    cases h : pairN a k with
    | none => rfl
    | some v =>
      cases v
      · show before k a (k :: L) = _
        rw [before_cons_first_left haL]; rfl
      · show before a k (k :: L) = _
        rw [before_cons_first_right (by omega) L]; rfl
  have hnew : ∀ L, L ∈ orders k → (allows (choiceNew lawN pairN k) (k :: L) = true ↔
      (∀ a b, a < b → b < k →
        (if lawN (a, b, k) = (2, 0) then false else pairChoice a b (indT (lawN (a, b, k))) L) = true) ∧
      (∀ a, a < k → (pairN a k != some true) = true)) := by
    intro L hL
    rw [allows_choiceNew]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a b hab hb => ?_, fun a ha => ?_⟩
      · have := h1 (a, b, k) (mem_newTriples.mpr ⟨hab, hb, rfl⟩)
        rw [htrip L hL a b hab hb] at this
        exact this
      · rw [← hpair L hL a ha]; exact h2 a ha
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, fun a ha => ?_⟩
      · obtain ⟨t1, t2, t3⟩ := mem_newTriples.mp ht
        obtain ⟨a, b, c⟩ := t
        simp only at t1 t2 t3
        subst t3
        rw [htrip L hL a b t1 t2]
        exact h1 a b t1 t2
      · rw [hpair L hL a ha]; exact h2 a ha
  by_cases hkill : (∃ a b, a < b ∧ b < k ∧ lawN (a, b, k) = (2, 0)) ∨ (∃ a, a < k ∧ pairN a k = some true)
  · right
    intro L hL
    rw [key L hL]
    have : allows (choiceNew lawN pairN k) (k :: L) = false := by
      cases h : allows (choiceNew lawN pairN k) (k :: L)
      · rfl
      · obtain ⟨h1, h2⟩ := (hnew L hL).mp h
        rcases hkill with ⟨a, b, hab, hb, hl⟩ | ⟨a, ha, hp⟩
        · have := h1 a b hab hb
          rw [if_pos hl] at this
          cases this
        · have := h2 a ha
          rw [hp] at this
          cases this
    rw [this, Bool.and_false]
  · have hk1 : ∀ a b, a < b → b < k → lawN (a, b, k) ≠ (2, 0) := fun a b hab hb h =>
      hkill (Or.inl ⟨a, b, hab, hb, h⟩)
    have hk2 : ∀ a, a < k → pairN a k ≠ some true := fun a ha h => hkill (Or.inr ⟨a, ha, h⟩)
    by_cases hconf : ∃ a b, a < b ∧ b < k ∧ conflictO (pairN a b) (indT (lawN (a, b, k))) = true
    · right
      intro L hL
      rw [key L hL]
      obtain ⟨a, b, hab, hb, hcf⟩ := hconf
      cases h1 : allows (choiceEPN lawN pairN k) L
      · rfl
      · cases h2 : allows (choiceNew lawN pairN k) (k :: L)
        · rfl
        · exfalso
          have hp1 := ((allows_choiceEPN lawN pairN L k).mp h1).2 a b hab hb
          have hp2 := ((hnew L hL).mp h2).1 a b hab hb
          rw [if_neg (hk1 a b hab hb)] at hp2
          have := pairChoice_conflict (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
            ((mem_of_mem_orders hL b).mpr hb) (by omega) hcf
          rw [hp1, hp2] at this
          cases this
    · left
      have hnc : ∀ a b, a < b → b < k → conflictO (pairN a b) (indT (lawN (a, b, k))) = false := by
        intro a b hab hb
        cases h : conflictO (pairN a b) (indT (lawN (a, b, k)))
        · rfl
        · exact absurd ⟨a, b, hab, hb, h⟩ hconf
      refine ⟨choiceEPN lawN (fun a b => if b < k then mergeO (pairN a b) (indT (lawN (a, b, k)))
        else pairN a b) k, isChoice_choiceEPN _ _ k (fun _ t _ _ => hlaw t), ?_⟩
      intro L hL
      rw [key L hL]
      apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true, allows_choiceEPN, allows_choiceEPN, hnew L hL]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, _⟩
        refine ⟨h1, fun a b hab hb => ?_⟩
        simp only [if_pos hb]
        rw [pairChoice_merge (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
          ((mem_of_mem_orders hL b).mpr hb) (by omega) (hnc a b hab hb), h2 a b hab hb, Bool.true_and]
        have := h3 a b hab hb
        rw [if_neg (hk1 a b hab hb)] at this
        exact this
      · rintro ⟨h1, h2⟩
        have hm : ∀ a b, a < b → b < k → pairChoice a b (pairN a b) L = true ∧
            pairChoice a b (indT (lawN (a, b, k))) L = true := by
          intro a b hab hb
          have := h2 a b hab hb
          simp only [if_pos hb] at this
          rw [pairChoice_merge (nodup_of_mem_orders hL) ((mem_of_mem_orders hL a).mpr (by omega))
            ((mem_of_mem_orders hL b).mpr hb) (by omega) (hnc a b hab hb), Bool.and_eq_true] at this
          exact this
        refine ⟨⟨h1, fun a b hab hb => (hm a b hab hb).1⟩, fun a b hab hb => ?_, fun a ha => ?_⟩
        · rw [if_neg (hk1 a b hab hb)]; exact (hm a b hab hb).2
        · cases h : pairN a k with
          | none => rfl
          | some v => cases v
                      · rfl
                      · exact absurd h (hk2 a ha)

/-! ### Relabelling domains and slices -/

/-- **Domains are closed under relabelling.** -/
theorem isDom_relabel {n : Nat} {p : List Nat → Bool} (hp : IsDom n p) {σ : List Nat} (hσ : σ ∈ orders n) :
    IsDom n (fun L => p (rlab σ L)) := by
  obtain ⟨c, hc, hpc⟩ := hp
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff n c hc
  have hfg : ∀ a, app (pinv n σ) (app σ a) = a := app_pinv_app hσ
  have hgf : ∀ a, app σ (app (pinv n σ) a) = a := app_app_pinv hσ
  have hn : ∀ a, a < n ↔ app σ a < n := fun a => (app_lt_iff hσ a).symm
  refine ⟨choiceEPN (lawT (app (pinv n σ)) (app σ) lawN) (pairT (app σ) pairN) n,
    isChoice_choiceEPN _ _ n (fun _ t _ _ => lawT_extreme hlaw t), ?_⟩
  intro L hL
  rw [allows_choiceEPN_relabel hfg hgf hn lawN pairN hL]
  exact hpc _ (rlab_mem_orders hσ hL)

theorem isEmptyOn_relabel {n : Nat} {p : List Nat → Bool} (hp : IsEmptyOn n p) {σ : List Nat}
    (hσ : σ ∈ orders n) : IsEmptyOn n (fun L => p (rlab σ L)) :=
  fun L hL => hp _ (rlab_mem_orders hσ hL)

/-- The permutation of `0..k-1` induced on a slice: `a ↦ down (π x) (π (up x a))`. -/
def slicePerm (k x : Nat) (π : List Nat) : List Nat :=
  (List.range k).map (fun a => down (app π x) (app π (up x a)))

theorem up_lt {x a k : Nat} (hx : x < k + 1) (ha : a < k) : up x a < k + 1 := by
  unfold up; split <;> omega

theorem down_lt {x b k : Nat} (hb : b < k + 1) (hbx : b ≠ x) (hx : x < k + 1) : down x b < k := by
  unfold down; split <;> omega

theorem slicePerm_mem {k x : Nat} {π : List Nat} (hπ : π ∈ orders (k + 1)) (hx : x < k + 1) :
    slicePerm k x π ∈ orders k := by
  have hπx := app_lt hπ hx
  have hφlt : ∀ a, a < k → down (app π x) (app π (up x a)) < k := fun a ha =>
    down_lt (app_lt hπ (up_lt hx ha)) (fun h => up_ne x a (app_injective hπ h)) hπx
  rw [mem_orders_iff]
  apply perm_of_nodup_of_mem_iff
  · unfold slicePerm
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab e => hab ?_) List.nodup_range
    have h1 := congrArg (up (app π x)) e
    rw [up_down (fun h => up_ne x a (app_injective hπ h)),
      up_down (fun h => up_ne x b (app_injective hπ h))] at h1
    exact up_injective x (app_injective hπ h1)
  · exact List.nodup_range
  · intro b
    rw [List.mem_range]
    unfold slicePerm
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hφlt a (List.mem_range.mp ha)
    · intro hb
      -- preimage of `up (π x) b`
      have hy : up (app π x) b < k + 1 := up_lt hπx hb
      obtain ⟨z, hz, hzy⟩ := exists_app_eq hπ hy
      have hzx : z ≠ x := fun h => by
        rw [h] at hzy
        exact up_ne (app π x) b hzy.symm
      refine ⟨down x z, List.mem_range.mpr (down_lt hz hzx hx), ?_⟩
      rw [up_down hzx, hzy, down_up]

theorem app_slicePerm {k x : Nat} {π : List Nat} (hπ : π ∈ orders (k + 1)) (hx : x < k + 1) {a : Nat}
    (ha : a < k) : app (slicePerm k x π) a = down (app π x) (app π (up x a)) := by
  have hmem := slicePerm_mem hπ hx
  rw [app_of_lt hmem ha]
  unfold slicePerm
  rw [List.getElem_map, List.getElem_range]

theorem map_up_slicePerm {k x : Nat} {π : List Nat} (hπ : π ∈ orders (k + 1)) (hx : x < k + 1)
    {L : List Nat} (hL : L ∈ orders k) :
    (rlab (slicePerm k x π) L).map (up (app π x)) = (L.map (up x)).map (app π) := by
  rw [rlab_eq_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro a ha
  have ha' := (mem_of_mem_orders hL a).mp ha
  simp only [Function.comp]
  rw [app_slicePerm hπ hx ha', up_down (fun h => up_ne x a (app_injective hπ h))]

/-- **Slices of a relabelled domain.** -/
theorem botP_relabel {k x : Nat} {π : List Nat} (hπ : π ∈ orders (k + 1)) (hx : x < k + 1)
    (H : List Nat → Bool) {L : List Nat} (hL : L ∈ orders k) :
    botP x (fun M => H (rlab π M)) L = botP (app π x) H (rlab (slicePerm k x π) L) := by
  show H (rlab π (L.map (up x) ++ [x])) = H ((rlab (slicePerm k x π) L).map (up (app π x)) ++ [app π x])
  rw [map_up_slicePerm hπ hx hL, rlab_eq_map, List.map_append]
  rfl

theorem topP_relabel {k y : Nat} {π : List Nat} (hπ : π ∈ orders (k + 1)) (hy : y < k + 1)
    (H : List Nat → Bool) {L : List Nat} (hL : L ∈ orders k) :
    topP y (fun M => H (rlab π M)) L = topP (app π y) H (rlab (slicePerm k y π) L) := by
  show H (rlab π (y :: L.map (up y))) = H (app π y :: (rlab (slicePerm k y π) L).map (up (app π y)))
  rw [map_up_slicePerm hπ hy hL, rlab_eq_map, List.map_cons]

/-- The transposition of `x` and `k` on labels. -/
def swapFn (k x a : Nat) : Nat := if a = x then k else if a = k then x else a

theorem swapFn_invol (k x a : Nat) : swapFn k x (swapFn k x a) = a := by
  unfold swapFn
  by_cases h1 : a = x
  · subst h1
    by_cases h3 : k = a
    · subst h3; simp
    · simp [h3]
  · by_cases h2 : a = k
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapFn_lt {k x a : Nat} (hx : x < k + 1) (ha : a < k + 1) : swapFn k x a < k + 1 := by
  unfold swapFn
  split
  · omega
  · split <;> omega

/-- The transposition of `x` and `k`, as a permutation of `0..k`. -/
def swapLast (k x : Nat) : List Nat := (List.range (k + 1)).map (swapFn k x)

theorem swapLast_mem {k x : Nat} (hx : x < k + 1) : swapLast k x ∈ orders (k + 1) := by
  rw [mem_orders_iff]
  apply perm_of_nodup_of_mem_iff
  · unfold swapLast
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} _ _ hab e => hab ?_) List.nodup_range
    have := congrArg (swapFn k x) e
    rwa [swapFn_invol, swapFn_invol] at this
  · exact List.nodup_range
  · intro b
    unfold swapLast
    rw [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact swapFn_lt hx (List.mem_range.mp ha)
    · intro hb
      exact ⟨swapFn k x b, List.mem_range.mpr (swapFn_lt hx hb), swapFn_invol k x b⟩

theorem app_swapLast_k {k x : Nat} (hx : x < k + 1) : app (swapLast k x) k = x := by
  rw [app_of_lt (swapLast_mem hx) (by omega)]
  unfold swapLast
  rw [List.getElem_map, List.getElem_range]
  unfold swapFn
  by_cases h : k = x
  · subst h; simp
  · simp [h]

/-- **Bottom slices of domains are domains or empty.** -/
theorem slice_bot {k x : Nat} (hx : x < k + 1) {H : List Nat → Bool} (hH : IsDom (k + 1) H) :
    IsDom k (botP x H) ∨ IsEmptyOn k (botP x H) := by
  have hπ := swapLast_mem hx
  have hψ := slicePerm_mem hπ (Nat.lt_succ_self k)
  have hψ' := pinv_mem_orders hψ
  have heq : ∀ L, L ∈ orders k → botP x H L =
      botP k (fun M => H (rlab (swapLast k x) M)) (rlab (pinv k (slicePerm k k (swapLast k x))) L) := by
    intro L hL
    have h1 := botP_relabel hπ (Nat.lt_succ_self k) H (rlab_mem_orders hψ' hL)
    rw [app_swapLast_k hx, rlab_rlab_pinv hψ] at h1
    exact h1.symm
  rcases slice_bot_last k (isDom_relabel hH hπ) with h | h
  · left
    obtain ⟨c, hc, hpc⟩ := isDom_relabel h hψ'
    exact ⟨c, hc, fun L hL => (heq L hL).trans (hpc L hL)⟩
  · right
    intro L hL
    rw [heq L hL]
    exact h _ (rlab_mem_orders hψ' hL)

/-- **Top slices of domains are domains or empty.** -/
theorem slice_top {k y : Nat} (hy : y < k + 1) {H : List Nat → Bool} (hH : IsDom (k + 1) H) :
    IsDom k (topP y H) ∨ IsEmptyOn k (topP y H) := by
  have hπ := swapLast_mem hy
  have hψ := slicePerm_mem hπ (Nat.lt_succ_self k)
  have hψ' := pinv_mem_orders hψ
  have heq : ∀ L, L ∈ orders k → topP y H L =
      topP k (fun M => H (rlab (swapLast k y) M)) (rlab (pinv k (slicePerm k k (swapLast k y))) L) := by
    intro L hL
    have h1 := topP_relabel hπ (Nat.lt_succ_self k) H (rlab_mem_orders hψ' hL)
    rw [app_swapLast_k hy, rlab_rlab_pinv hψ] at h1
    exact h1.symm
  rcases slice_top_last k (isDom_relabel hH hπ) with h | h
  · left
    obtain ⟨c, hc, hpc⟩ := isDom_relabel h hψ'
    exact ⟨c, hc, fun L hL => (heq L hL).trans (hpc L hL)⟩
  · right
    intro L hL
    rw [heq L hL]
    exact h _ (rlab_mem_orders hψ' hL)

end CDCert.K6
