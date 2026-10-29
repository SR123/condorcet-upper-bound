/-
CDCert.K6.Concat — **ordered concatenation of domains**. For an `n`-domain `K` and an `n'`-domain
`K'`, `concat n K K'` is the `(n + n')`-domain of the orders `L₁ ++ L₂'`, where `L₁ ∈ K` and `L₂'` is an
order of `K'` with every label shifted by `n` (every alternative of the first block above every
alternative of the second).

* `perm_split`: the orders with the labels `< n` first are exactly the joins `joinL n L₁ L₂`;
* `card_concat`: `|K ⊕ K'| = |K| |K'|`;
* `adj_concat`: `A(K ⊕ K') = A(K) |K'| + |K| A(K')` (a swap across the two blocks is never enabled);
* `isDom_concat`: the concatenation of two `groupsEP` domains is a `groupsEP` domain (block laws and
  pairs, the laws `c` never first / `a` never last on crossing triples, fixed crossing pairs).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Win

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### Joining orders -/

/-- The order `L₁` followed by `L₂` with its labels shifted by `n`. -/
def joinL (n : Nat) (L1 L2 : List Nat) : List Nat := L1 ++ L2.map (fun x => n + x)

/-- The labels `< n` come first. -/
def splitOK (n : Nat) (L : List Nat) : Bool :=
  decide (L = L.filter (fun x => decide (x < n)) ++ L.filter (fun x => decide (n ≤ x)))

/-- **Ordered concatenation** of an `n`-domain and an `n'`-domain. -/
def concat (n : Nat) (K K' : List Nat → Bool) : List Nat → Bool := fun L =>
  splitOK n L && K (L.filter (fun x => decide (x < n))) &&
    K' ((L.filter (fun x => decide (n ≤ x))).map (fun x => x - n))

theorem range_filter_lt (n n' : Nat) : (List.range (n + n')).filter (fun x => decide (x < n)) = List.range n := by
  rw [List.range_add, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp
  · intro a ha
    simpa using List.mem_range.mp ha

theorem range_filter_ge (n n' : Nat) :
    (List.range (n + n')).filter (fun x => decide (n ≤ x)) = (List.range n').map (fun x => n + x) := by
  rw [List.range_add, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr, List.nil_append]
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp
  · intro a ha
    have := List.mem_range.mp ha
    simp only [decide_eq_true_eq]
    omega

theorem joinL_mem {n n' : Nat} {L1 L2 : List Nat} (h1 : L1 ∈ orders n) (h2 : L2 ∈ orders n') :
    joinL n L1 L2 ∈ orders (n + n') := by
  rw [mem_orders_iff] at h1 h2 ⊢
  unfold joinL
  rw [List.range_add]
  exact h1.append (h2.map _)

theorem filter_joinL_lt {n : Nat} {L1 : List Nat} (h1 : L1 ∈ orders n) (L2 : List Nat) :
    (joinL n L1 L2).filter (fun x => decide (x < n)) = L1 := by
  unfold joinL
  rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp
  · intro a ha
    simpa using (mem_of_mem_orders h1 a).mp ha

theorem filter_joinL_ge {n : Nat} {L1 : List Nat} (h1 : L1 ∈ orders n) (L2 : List Nat) :
    (joinL n L1 L2).filter (fun x => decide (n ≤ x)) = L2.map (fun x => n + x) := by
  unfold joinL
  rw [List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr, List.nil_append]
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp
  · intro a ha
    have := (mem_of_mem_orders h1 a).mp ha
    simp only [decide_eq_true_eq]
    omega

theorem map_shift_sub (n : Nat) (L2 : List Nat) : (L2.map (fun x => n + x)).map (fun x => x - n) = L2 := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id L2]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp, id]
  omega

theorem splitOK_joinL {n : Nat} {L1 : List Nat} (h1 : L1 ∈ orders n) (L2 : List Nat) :
    splitOK n (joinL n L1 L2) = true := by
  unfold splitOK
  rw [filter_joinL_lt h1, filter_joinL_ge h1]
  exact decide_eq_true rfl

theorem concat_joinL {n : Nat} {L1 : List Nat} (h1 : L1 ∈ orders n) (L2 : List Nat) (K K' : List Nat → Bool) :
    concat n K K' (joinL n L1 L2) = (K L1 && K' L2) := by
  unfold concat
  rw [splitOK_joinL h1, filter_joinL_lt h1, filter_joinL_ge h1, map_shift_sub, Bool.true_and]

theorem joinL_inj {n : Nat} {L1 L1' L2 L2' : List Nat} (h1 : L1 ∈ orders n) (h1' : L1' ∈ orders n)
    (h : joinL n L1 L2 = joinL n L1' L2') : L1 = L1' ∧ L2 = L2' := by
  have e1 : L1 = L1' := by
    have := congrArg (List.filter (fun x => decide (x < n))) h
    rw [filter_joinL_lt h1, filter_joinL_lt h1'] at this
    exact this
  refine ⟨e1, ?_⟩
  have := congrArg (fun L => (L.filter (fun x => decide (n ≤ x))).map (fun x => x - n)) h
  simp only at this
  rw [filter_joinL_ge h1, filter_joinL_ge h1', map_shift_sub, map_shift_sub] at this
  exact this

theorem nodup_filter' {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup :=
  (List.filter_sublist).nodup h

/-- The orders with the labels `< n` first are the joins. -/
theorem perm_split (n n' : Nat) : ((orders (n + n')).filter (splitOK n)).Perm
    ((orders n).flatMap (fun L1 => (orders n').map (joinL n L1))) := by
  apply perm_of_nodup_of_mem_iff' (nodup_filter' _ (orders_nodup _))
  · apply nodup_flatMap_of (orders_nodup n)
    · intro L1 h1
      exact nodup_map_of_inj (fun a b h => (joinL_inj h1 h1 h).2) (orders_nodup n')
    · intro L1 h1 L1' h1' hne x hx hx'
      obtain ⟨L2, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨L2', _, he⟩ := List.mem_map.mp hx'
      exact hne (joinL_inj h1' h1 he).1.symm
  · intro L
    rw [List.mem_filter, List.mem_flatMap]
    constructor
    · rintro ⟨hL, hs⟩
      have hp := mem_orders_iff.mp hL
      refine ⟨L.filter (fun x => decide (x < n)), ?_, List.mem_map.mpr
        ⟨(L.filter (fun x => decide (n ≤ x))).map (fun x => x - n), ?_, ?_⟩⟩
      · rw [mem_orders_iff, ← range_filter_lt n n']
        exact hp.filter _
      · rw [mem_orders_iff, ← map_shift_sub n (List.range n'), ← range_filter_ge n n']
        exact (hp.filter _).map _
      · unfold joinL
        rw [List.map_map]
        have e : (L.filter (fun x => decide (n ≤ x))).map ((fun x => n + x) ∘ (fun x => x - n)) =
            L.filter (fun x => decide (n ≤ x)) := by
          conv => rhs; rw [← List.map_id (L.filter (fun x => decide (n ≤ x)))]
          apply List.map_congr_left
          intro a ha
          have := (List.mem_filter.mp ha).2
          simp only [decide_eq_true_eq] at this
          simp only [Function.comp, id]
          omega
        rw [e]
        exact (of_decide_eq_true hs).symm
    · rintro ⟨L1, h1, hL⟩
      obtain ⟨L2, h2, rfl⟩ := List.mem_map.mp hL
      exact ⟨joinL_mem h1 h2, splitOK_joinL h1 L2⟩

theorem concat_splitOK {n : Nat} {K K' : List Nat → Bool} {L : List Nat} (h : concat n K K' L = true) :
    splitOK n L = true := by
  unfold concat at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

/-- Counting over the orders whose labels `< n` come first. -/
theorem countP_split {n n' : Nat} (P : List Nat → Bool) (hP : ∀ L, P L = true → splitOK n L = true) :
    (orders (n + n')).countP P = ((orders n).map (fun L1 => (orders n').countP (fun L2 => P (joinL n L1 L2)))).sum := by
  have e1 : (orders (n + n')).countP P = ((orders (n + n')).filter (splitOK n)).countP P := by
    rw [List.countP_filter]
    apply List.countP_congr
    intro L _
    constructor
    · intro h; rw [h, hP L h]; rfl
    · intro h; exact ((Bool.and_eq_true _ _).mp h).1
  rw [e1, (perm_split n n').countP_eq, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro L1 _
  simp only [Function.comp]
  rw [List.countP_map]
  rfl

theorem nsum_ite_const {α : Type} (l : List α) (p : α → Bool) (c : Nat) :
    (l.map (fun a => if p a = true then c else 0)).sum = l.countP p * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a = true
    · rw [if_pos h, if_pos h, Nat.add_mul, Nat.one_mul]; omega
    · rw [if_neg h, if_neg h]; simp

/-- **`|K ⊕ K'| = |K| |K'|`.** -/
theorem card_concat (n n' : Nat) (K K' : List Nat → Bool) :
    card (n + n') (concat n K K') = card n K * card n' K' := by
  unfold card
  rw [countP_split _ (fun L h => concat_splitOK h)]
  have e : ∀ L1, L1 ∈ orders n → (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2)) =
      if K L1 = true then (orders n').countP K' else 0 := by
    intro L1 h1
    have : (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2)) = (orders n').countP (fun L2 => K L1 && K' L2) :=
      List.countP_congr (fun L2 _ => by rw [concat_joinL h1])
    rw [this]
    by_cases hK : K L1 = true
    · rw [if_pos hK]
      exact List.countP_congr (fun L2 _ => by rw [hK, Bool.true_and])
    · rw [if_neg hK]
      have hK' : K L1 = false := by cases h : K L1; rfl; exact absurd h hK
      rw [List.countP_eq_zero]
      intro L2 _
      rw [hK', Bool.false_and]
      exact Bool.false_ne_true
  rw [List.map_congr_left e, nsum_ite_const]

/-! ### Enabled swaps of a concatenation -/

theorem swapAt_append_right : ∀ (L1 M : List Nat) (q : Nat), swapAt (L1.length + q) (L1 ++ M) = L1 ++ swapAt q M
  | [], M, q => by simp
  | a :: L1, M, q => by
    rw [List.length_cons, show L1.length + 1 + q = (L1.length + q) + 1 by omega, List.cons_append, swapAt_cons,
      swapAt_append_right L1 M q]
    rfl

theorem swapAt_joinL_left {n : Nat} {L1 : List Nat} (h1 : L1 ∈ orders n) (L2 : List Nat) {p : Nat} (hp : p + 1 < n) :
    swapAt p (joinL n L1 L2) = joinL n (swapAt p L1) L2 := by
  unfold joinL
  exact swapAt_append _ (by rw [length_of_mem_orders h1]; exact hp)

theorem swapAt_joinL_right {n n' : Nat} {L1 L2 : List Nat} (h1 : L1 ∈ orders n) (h2 : L2 ∈ orders n') {q : Nat}
    (hq : q + 1 < n') : swapAt (n + q) (joinL n L1 L2) = joinL n L1 (swapAt q L2) := by
  unfold joinL
  have := swapAt_append_right L1 (L2.map (fun x => n + x)) q
  rw [length_of_mem_orders h1] at this
  rw [this, swapAt_map _ (by rw [length_of_mem_orders h2]; exact hq)]

theorem adjAt_concat_left (n n' : Nat) (K K' : List Nat → Bool) {p : Nat} (hp : p + 1 < n) :
    adjAt (n + n') p (concat n K K') = adjAt n p K * card n' K' := by
  unfold adjAt card
  rw [countP_split _ (fun L h => concat_splitOK ((Bool.and_eq_true _ _).mp h).1)]
  have e : ∀ L1, L1 ∈ orders n →
      (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2) && concat n K K' (swapAt p (joinL n L1 L2))) =
        if (K L1 && K (swapAt p L1)) = true then (orders n').countP K' else 0 := by
    intro L1 h1
    have hs : swapAt p L1 ∈ orders n := swapAt_mem_orders hp h1
    have : (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2) && concat n K K' (swapAt p (joinL n L1 L2))) =
        (orders n').countP (fun L2 => (K L1 && K (swapAt p L1)) && K' L2) := by
      apply List.countP_congr
      intro L2 _
      rw [swapAt_joinL_left h1 L2 hp, concat_joinL h1, concat_joinL hs]
      cases K L1 <;> cases K (swapAt p L1) <;> cases K' L2 <;> simp
    rw [this]
    by_cases hK : (K L1 && K (swapAt p L1)) = true
    · rw [if_pos hK]
      exact List.countP_congr (fun L2 _ => by rw [hK, Bool.true_and])
    · rw [if_neg hK, List.countP_eq_zero]
      intro L2 _ h
      rw [Bool.and_eq_true] at h
      exact hK h.1
  rw [List.map_congr_left e, nsum_ite_const]

theorem adjAt_concat_right (n n' : Nat) (K K' : List Nat → Bool) {q : Nat} (hq : q + 1 < n') :
    adjAt (n + n') (n + q) (concat n K K') = card n K * adjAt n' q K' := by
  unfold adjAt card
  rw [countP_split _ (fun L h => concat_splitOK ((Bool.and_eq_true _ _).mp h).1)]
  have e : ∀ L1, L1 ∈ orders n →
      (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2) && concat n K K' (swapAt (n + q) (joinL n L1 L2))) =
        if K L1 = true then (orders n').countP (fun L2 => K' L2 && K' (swapAt q L2)) else 0 := by
    intro L1 h1
    have : (orders n').countP (fun L2 => concat n K K' (joinL n L1 L2) && concat n K K' (swapAt (n + q) (joinL n L1 L2))) =
        (orders n').countP (fun L2 => K L1 && (K' L2 && K' (swapAt q L2))) := by
      apply List.countP_congr
      intro L2 h2
      rw [swapAt_joinL_right h1 h2 hq, concat_joinL h1, concat_joinL h1]
      cases K L1 <;> cases K' L2 <;> cases K' (swapAt q L2) <;> simp
    rw [this]
    by_cases hK : K L1 = true
    · rw [if_pos hK]
      exact List.countP_congr (fun L2 _ => by rw [hK, Bool.true_and])
    · rw [if_neg hK, List.countP_eq_zero]
      intro L2 _ h
      rw [Bool.and_eq_true] at h
      exact hK h.1
  rw [List.map_congr_left e, nsum_ite_const, Nat.mul_comm]

theorem getElem_swapAt_left {M : List Nat} {j : Nat} (hj : j + 1 < M.length) :
    (swapAt j M)[j]'(by unfold swapAt; rw [List.length_set, List.length_set]; omega) = M[j + 1] := by
  unfold swapAt
  rw [List.getElem_set, if_neg (by omega), List.getElem_set, if_pos rfl, getD_of_lt hj]

theorem length_filter_lt {n n' : Nat} {L : List Nat} (hL : L ∈ orders (n + n')) :
    (L.filter (fun x => decide (x < n))).length = n := by
  have := ((mem_orders_iff.mp hL).filter (fun x => decide (x < n))).length_eq
  rw [range_filter_lt, List.length_range] at this
  exact this

/-- A swap across the two blocks is never enabled. -/
theorem adjAt_concat_mid (n n' : Nat) (K K' : List Nat → Bool) (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    adjAt (n + n') (n - 1) (concat n K K') = 0 := by
  unfold adjAt
  rw [List.countP_eq_zero]
  intro L hL h
  rw [Bool.and_eq_true] at h
  have hs := concat_splitOK h.2
  have hs0 := concat_splitOK h.1
  have hlen : L.length = n + n' := length_of_mem_orders hL
  have hsw : swapAt (n - 1) L ∈ orders (n + n') := swapAt_mem_orders (by omega) hL
  -- the entry at position n - 1 after the swap is the old entry at n, which is ≥ n
  have hge : n ≤ L[n]'(by omega) := by
    have e := of_decide_eq_true hs0
    have hl1 := length_filter_lt hL
    have hmem : L[n]'(by omega) ∈ L.filter (fun x => decide (n ≤ x)) := by
      have : L[n]'(by omega) = (L.filter (fun x => decide (x < n)) ++ L.filter (fun x => decide (n ≤ x)))[n]'(by
          rw [← e]; omega) := by
        congr 1
      rw [this, List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := (List.mem_filter.mp hmem).2
    simpa using this
  have hlt : (swapAt (n - 1) L)[n - 1]'(by rw [length_of_mem_orders hsw]; omega) < n := by
    have e := of_decide_eq_true hs
    have hl1 := length_filter_lt hsw
    have : (swapAt (n - 1) L)[n - 1]'(by rw [length_of_mem_orders hsw]; omega) =
        ((swapAt (n - 1) L).filter (fun x => decide (x < n)) ++
          (swapAt (n - 1) L).filter (fun x => decide (n ≤ x)))[n - 1]'(by
          rw [List.length_append, hl1]; omega) := by
      congr 1
    rw [this, List.getElem_append_left (by omega)]
    have hm := List.getElem_mem (l := (swapAt (n - 1) L).filter (fun x => decide (x < n))) (n := n - 1) (by omega)
    have := (List.mem_filter.mp hm).2
    simpa using this
  have hsame := getElem_swapAt_left (M := L) (j := n - 1) (by omega)
  have hidx : L[n - 1 + 1]'(by omega) = L[n]'(by omega) := by congr 1; omega
  rw [hsame, hidx] at hlt
  omega

theorem nsum_append' (l1 l2 : List Nat) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons a l ih => rw [List.cons_append, List.sum_cons, List.sum_cons, ih, Nat.add_assoc]

theorem nsum_map_mul_right' {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map (fun a => f a * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, Nat.add_mul]

theorem nsum_map_mul_left' {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, Nat.mul_add]

/-- **`A(K ⊕ K') = A(K) |K'| + |K| A(K')`.** -/
theorem adj_concat (n n' : Nat) (K K' : List Nat → Bool) (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    adj (n + n') (concat n K K') = adj n K * card n' K' + card n K * adj n' K' := by
  unfold adj
  have hr : n + n' - 1 = (n - 1) + 1 + (n' - 1) := by omega
  rw [hr, List.range_add, List.range_add, List.map_append, List.map_append, nsum_append', nsum_append',
    List.map_map, List.map_map]
  have e1 : ((List.range (n - 1)).map (fun j => adjAt (n + n') j (concat n K K'))).sum =
      ((List.range (n - 1)).map (fun j => adjAt n j K)).sum * card n' K' := by
    rw [← nsum_map_mul_right']
    exact congrArg List.sum (List.map_congr_left (fun j hj => adjAt_concat_left n n' K K'
      (by have := List.mem_range.mp hj; omega)))
  have e2 : ((List.range 1).map ((fun j => adjAt (n + n') j (concat n K K')) ∘ fun x => n - 1 + x)).sum = 0 := by
    simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp, Nat.add_zero]
    rw [adjAt_concat_mid n n' K K' hn hn']
  have e3 : ((List.range (n' - 1)).map ((fun j => adjAt (n + n') j (concat n K K')) ∘ fun x => n - 1 + 1 + x)).sum =
      card n K * ((List.range (n' - 1)).map (fun j => adjAt n' j K')).sum := by
    rw [← nsum_map_mul_left']
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp]
    rw [show n - 1 + 1 + q = n + q by omega]
    exact adjAt_concat_right n n' K K' (by have := List.mem_range.mp hq; omega)
  rw [e1, e2, e3, Nat.add_zero]

/-! ### The concatenation is a `groupsEP` domain -/

theorem holdsL_map (f : Nat → Nat) (hf : Function.Injective f) (a b c : Nat) (law : Fin 3 × Fin 3) (L : List Nat) :
    holdsL (f a) (f b) (f c) law (L.map f) = holdsL a b c law L := by
  unfold holdsL
  split
  · exact neverL_map f hf a b c _ L
  · split
    · exact neverL_map f hf b a c _ L
    · exact neverL_map f hf c a b _ L

theorem pairChoice_filter (q : Nat → Bool) {a c : Nat} (ha : q a = true) (hc : q c = true) (o : Option Bool)
    (L : List Nat) : pairChoice a c o (L.filter q) = pairChoice a c o L := by
  cases o with
  | none => rfl
  | some b =>
    cases b with
    | true => exact pairL_filter q ha hc L
    | false => exact pairL_filter q hc ha L

theorem pairChoice_map (f : Nat → Nat) (hf : Function.Injective f) (a c : Nat) (o : Option Bool) (L : List Nat) :
    pairChoice (f a) (f c) o (L.map f) = pairChoice a c o L := by
  cases o with
  | none => rfl
  | some b =>
    cases b with
    | true => exact before_map f hf a c L
    | false => exact before_map f hf c a L

theorem before_cross {a c : Nat} : ∀ {F1 F2 : List Nat}, a ∈ F1 → c ∈ F2 → c ∉ F1 → before a c (F1 ++ F2) = true
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | y :: F1, F2, ha, hc, hcn => by
    rw [List.cons_append, before_cons]
    by_cases hya : y = a
    · rw [if_pos hya]
      exact decide_eq_true (List.mem_append_right _ hc)
    · rw [if_neg hya]
      have hyc : y ≠ c := fun h => hcn (h ▸ List.mem_cons_self)
      rw [if_neg hyc]
      exact before_cross ((List.mem_cons.mp ha).resolve_left (fun h => hya h.symm)) hc
        (fun h => hcn (List.mem_cons_of_mem _ h))

/-- Labels `< n` before labels `≥ n` in every pair: the list is split. -/
theorem split_of_cross (n : Nat) : ∀ (L : List Nat), L.Nodup →
    (∀ a c, a < n → n ≤ c → a ∈ L → c ∈ L → before a c L = true) →
    L = L.filter (fun x => decide (x < n)) ++ L.filter (fun x => decide (n ≤ x))
  | [], _, _ => rfl
  | x :: L, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    have ih := split_of_cross n L hnd'.2 (fun a c ha hc haL hcL => by
      have := h a c ha hc (List.mem_cons_of_mem _ haL) (List.mem_cons_of_mem _ hcL)
      rw [before_cons] at this
      have hxa : x ≠ a := fun e => hnd'.1 (e ▸ haL)
      have hxc : x ≠ c := fun e => hnd'.1 (e ▸ hcL)
      rw [if_neg hxa, if_neg hxc] at this
      exact this)
    by_cases hx : x < n
    · rw [List.filter_cons_of_pos (by simpa using hx), List.filter_cons_of_neg (by simpa using hx),
        List.cons_append, ← ih]
    · -- no label `< n` after `x`
      have hnone : L.filter (fun y => decide (y < n)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a haL ha
        have ha' : a < n := by simpa using ha
        have := h a x ha' (by omega) (List.mem_cons_of_mem _ haL) List.mem_cons_self
        rw [before_cons] at this
        have hxa : x ≠ a := fun e => hnd'.1 (e ▸ haL)
        rw [if_neg hxa, if_pos rfl] at this
        cases this
      rw [List.filter_cons_of_neg (by simpa using hx), List.filter_cons_of_pos (by simpa using (show n ≤ x by omega)),
        hnone, List.nil_append]
      congr 1
      have e := ih
      rw [hnone, List.nil_append] at e
      exact e

/-- The laws of a concatenation. -/
def lawCat (n : Nat) (lawN lawN' : Nat × Nat × Nat → Fin 3 × Fin 3) (t : Nat × Nat × Nat) : Fin 3 × Fin 3 :=
  if t.2.2 < n then lawN t else if n ≤ t.1 then lawN' (t.1 - n, t.2.1 - n, t.2.2 - n)
  else if t.2.1 < n then (2, 0) else (0, 2)

/-- The fixed pairs of a concatenation. -/
def pairCat (n : Nat) (pairN pairN' : Nat → Nat → Option Bool) (a c : Nat) : Option Bool :=
  if c < n then pairN a c else if n ≤ a then pairN' (a - n) (c - n) else some true

theorem shift_inj (n : Nat) : Function.Injective (fun x : Nat => n + x) := fun a b h => by simpa using h

/-- The two blocks of a split order. -/
theorem split_blocks {n n' : Nat} {L : List Nat} (hL : L ∈ orders (n + n')) :
    L.filter (fun x => decide (x < n)) ∈ orders n ∧
      (L.filter (fun x => decide (n ≤ x))).map (fun x => x - n) ∈ orders n' ∧
      ((L.filter (fun x => decide (n ≤ x))).map (fun x => x - n)).map (fun x => n + x) =
        L.filter (fun x => decide (n ≤ x)) := by
  have hp := mem_orders_iff.mp hL
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_orders_iff, ← range_filter_lt n n']
    exact hp.filter _
  · rw [mem_orders_iff, ← map_shift_sub n (List.range n'), ← range_filter_ge n n']
    exact (hp.filter _).map _
  · rw [List.map_map]
    conv => rhs; rw [← List.map_id (L.filter (fun x => decide (n ≤ x)))]
    apply List.map_congr_left
    intro a ha
    have := (List.mem_filter.mp ha).2
    simp only [decide_eq_true_eq] at this
    simp only [Function.comp, id]
    omega

theorem holdsL_low {n : Nat} {L : List Nat} {a b c : Nat} (ha : a < n) (hb : b < n) (hc : c < n)
    (law : Fin 3 × Fin 3) : holdsL a b c law (L.filter (fun x => decide (x < n))) = holdsL a b c law L :=
  holdsL_filter _ (by simpa using ha) (by simpa using hb) (by simpa using hc) law L

theorem holdsL_high {n : Nat} {L L2 : List Nat} (h3 : L2.map (fun x => n + x) = L.filter (fun x => decide (n ≤ x)))
    (a b c : Nat) (law : Fin 3 × Fin 3) : holdsL (n + a) (n + b) (n + c) law L = holdsL a b c law L2 := by
  rw [← holdsL_filter (fun x => decide (n ≤ x)) (by simp) (by simp) (by simp) law L, ← h3,
    holdsL_map _ (shift_inj n)]

theorem pairChoice_low {n : Nat} {L : List Nat} {a c : Nat} (ha : a < n) (hc : c < n) (o : Option Bool) :
    pairChoice a c o (L.filter (fun x => decide (x < n))) = pairChoice a c o L :=
  pairChoice_filter _ (by simpa using ha) (by simpa using hc) o L

theorem pairChoice_high {n : Nat} {L L2 : List Nat} (h3 : L2.map (fun x => n + x) = L.filter (fun x => decide (n ≤ x)))
    (a c : Nat) (o : Option Bool) : pairChoice (n + a) (n + c) o L = pairChoice a c o L2 := by
  rw [← pairChoice_filter (fun x => decide (n ≤ x)) (by simp) (by simp) o L, ← h3, pairChoice_map _ (shift_inj n)]

/-- **The concatenation of two `groupsEP` domains is a `groupsEP` domain.** -/
theorem isDom_concat {n n' : Nat} {K K' : List Nat → Bool} (hK : IsDom n K) (hK' : IsDom n' K') :
    IsDom (n + n') (concat n K K') := by
  obtain ⟨c, hc, hKc⟩ := hK
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff n c hc
  obtain ⟨c', hc', hKc'⟩ := hK'
  obtain ⟨lawN', pairN', hlaw', rfl⟩ := isChoice_groupsEP_iff n' c' hc'
  have hlawC : ∀ t, lawCat n lawN lawN' t ∈ lawsExtreme := by
    intro t
    unfold lawCat
    split
    · exact hlaw t
    · split
      · exact hlaw' _
      · split
        · decide
        · decide
  refine ⟨choiceEPN (lawCat n lawN lawN') (pairCat n pairN pairN') (n + n'),
    isChoice_choiceEPN _ _ (n + n') (fun _ t _ _ => hlawC t), ?_⟩
  intro L hL
  obtain ⟨h1, h2, h3⟩ := split_blocks hL
  have hnd := nodup_of_mem_orders hL
  have hmem : ∀ a, a ∈ L ↔ a < n + n' := mem_of_mem_orders hL
  have hA1 : K (L.filter (fun x => decide (x < n))) = true ↔
      (∀ t, t ∈ triplesN n → holdsL t.1 t.2.1 t.2.2 (lawN t) (L.filter (fun x => decide (x < n))) = true) ∧
      (∀ a c, a < c → c < n → pairChoice a c (pairN a c) (L.filter (fun x => decide (x < n))) = true) := by
    rw [hKc _ h1, allows_choiceEPN]
  have hA2 : K' ((L.filter (fun x => decide (n ≤ x))).map (fun x => x - n)) = true ↔
      (∀ t, t ∈ triplesN n' → holdsL t.1 t.2.1 t.2.2 (lawN' t)
        ((L.filter (fun x => decide (n ≤ x))).map (fun x => x - n)) = true) ∧
      (∀ a c, a < c → c < n' → pairChoice a c (pairN' a c)
        ((L.filter (fun x => decide (n ≤ x))).map (fun x => x - n)) = true) := by
    rw [hKc' _ h2, allows_choiceEPN]
  rw [Bool.eq_iff_iff, allows_choiceEPN]
  unfold concat
  rw [Bool.and_eq_true, Bool.and_eq_true, hA1, hA2]
  constructor
  · rintro ⟨⟨hs, ⟨hT1, hP1⟩⟩, ⟨hT2, hP2⟩⟩
    have hsplit := of_decide_eq_true hs
    have hcross : ∀ a c, a < n → n ≤ c → c < n + n' → before a c L = true := by
      intro a c ha hc hcn
      rw [hsplit]
      exact before_cross (List.mem_filter.mpr ⟨(hmem a).mpr (by omega), by simpa using ha⟩)
        (List.mem_filter.mpr ⟨(hmem c).mpr hcn, by simpa using hc⟩)
        (fun h => by have := (List.mem_filter.mp h).2; simp only [decide_eq_true_eq] at this; omega)
    refine ⟨fun t ht => ?_, fun a c hac hcn => ?_⟩
    · obtain ⟨a, b, c⟩ := t
      obtain ⟨hab, hbc, hcn⟩ := mem_triplesN.mp ht
      simp only at hab hbc hcn ⊢
      unfold lawCat
      simp only
      by_cases h4 : c < n
      · rw [if_pos h4, ← holdsL_low (L := L) (by omega) (by omega) h4]
        exact hT1 (a, b, c) (mem_triplesN.mpr ⟨hab, hbc, h4⟩)
      · rw [if_neg h4]
        by_cases h5 : n ≤ a
        · rw [if_pos h5]
          have := hT2 (a - n, b - n, c - n) (mem_triplesN.mpr ⟨by simp only; omega, by simp only; omega,
            by simp only; omega⟩)
          rw [← holdsL_high h3] at this
          simp only at this
          rw [show n + (a - n) = a by omega, show n + (b - n) = b by omega, show n + (c - n) = c by omega] at this
          exact this
        · rw [if_neg h5]
          by_cases h6 : b < n
          · rw [if_pos h6]
            show (if (2 : Fin 3) = 0 then neverL a b c 0 else if (2 : Fin 3) = 1 then neverL b a c 0
              else neverL c a b 0) L = true
            rw [if_neg (by decide), if_neg (by decide)]
            show (if (0 : Fin 3) = 0 then !(before c a L && before c b L) else _) = true
            rw [if_pos rfl, before_asymm hnd (hcross a c (by omega) (by omega) hcn), Bool.false_and]
            rfl
          · rw [if_neg h6]
            show (if (0 : Fin 3) = 0 then neverL a b c 2 else if (0 : Fin 3) = 1 then neverL b a c 2
              else neverL c a b 2) L = true
            rw [if_pos rfl]
            show (if (2 : Fin 3) = 0 then _ else if (2 : Fin 3) = 1 then _ else (before a b L || before a c L)) = true
            rw [if_neg (by decide), if_neg (by decide), hcross a b (by omega) (by omega) (by omega), Bool.true_or]
    · unfold pairCat
      by_cases h4 : c < n
      · rw [if_pos h4, ← pairChoice_low (L := L) (by omega) h4]
        exact hP1 a c hac h4
      · rw [if_neg h4]
        by_cases h5 : n ≤ a
        · rw [if_pos h5]
          have := hP2 (a - n) (c - n) (by omega) (by omega)
          rw [← pairChoice_high h3, show n + (a - n) = a by omega, show n + (c - n) = c by omega] at this
          exact this
        · rw [if_neg h5]
          exact hcross a c (by omega) (by omega) hcn
  · rintro ⟨hT, hP⟩
    have hcross : ∀ a c, a < n → n ≤ c → a ∈ L → c ∈ L → before a c L = true := by
      intro a c ha hc _ hcL
      have hcn := (hmem c).mp hcL
      have := hP a c (by omega) hcn
      unfold pairCat at this
      rw [if_neg (by omega), if_neg (by omega)] at this
      exact this
    refine ⟨⟨decide_eq_true (split_of_cross n L hnd hcross), fun t ht => ?_, fun a c hac hcn => ?_⟩,
      fun t ht => ?_, fun a c hac hcn => ?_⟩
    · obtain ⟨a, b, c⟩ := t
      obtain ⟨hab, hbc, hcn⟩ := mem_triplesN.mp ht
      simp only at hab hbc hcn ⊢
      rw [holdsL_low (by omega) (by omega) hcn]
      have := hT (a, b, c) (mem_triplesN.mpr ⟨hab, hbc, by simp only; omega⟩)
      unfold lawCat at this
      simp only at this
      rw [if_pos hcn] at this
      exact this
    · rw [pairChoice_low (by omega) hcn]
      have := hP a c hac (by omega)
      unfold pairCat at this
      rw [if_pos hcn] at this
      exact this
    · obtain ⟨a, b, c⟩ := t
      obtain ⟨hab, hbc, hcn⟩ := mem_triplesN.mp ht
      simp only at hab hbc hcn ⊢
      rw [← holdsL_high h3]
      have := hT (n + a, n + b, n + c) (mem_triplesN.mpr ⟨by simp only; omega, by simp only; omega,
        by simp only; omega⟩)
      unfold lawCat at this
      simp only at this
      rw [if_neg (by omega), if_pos (by omega)] at this
      rw [show n + a - n = a by omega, show n + b - n = b by omega, show n + c - n = c by omega] at this
      exact this
    · rw [← pairChoice_high h3]
      have := hP (n + a) (n + c) (by omega) (by omega)
      unfold pairCat at this
      rw [if_neg (by omega), if_pos (by omega), show n + a - n = a by omega, show n + c - n = c by omega] at this
      exact this

end CDCert.K6
