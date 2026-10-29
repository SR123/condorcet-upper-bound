/-
CDCert.K6.TabSemB — generic lemmas for reading the five-table: swaps of orders are
orders (`swapAt_mem_orders`), features of predicates agreeing on orders, the table's
counting functions `cardOf`, `a5Of`, `a53Of` on lists of orders (`cardOf_aux`, ...),
`fieldsOK_sound`, and the table readings `ty5` (type index) and `pot5` (scaled weight).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Feat
import CDCert.K6.DefsT
import CDCert.K6.SumInv
import CDCert.K6.Tab.Aux

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

/-! ### Swaps of orders are orders -/

/-- Exchange two labels. -/
def tswap (a b x : Nat) : Nat := if x = a then b else if x = b then a else x

theorem tswap_tswap {a b : Nat} (x : Nat) : tswap a b (tswap a b x) = x := by
  unfold tswap
  by_cases h1 : x = a
  · subst h1
    by_cases h2 : b = x
    · subst h2; simp
    · simp [h2, Ne.symm h2]
  · by_cases h2 : x = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapAt_getElem {j : Nat} {L : List Nat} (hj : j + 1 < L.length) (i : Nat)
    (hi : i < (swapAt j L).length) (hi' : i < L.length) :
    (swapAt j L)[i] = if i = j + 1 then L[j]'(by omega) else if i = j then L[j + 1] else L[i] := by
  unfold swapAt
  simp only [List.getElem_set, getD_of_lt hj, getD_of_lt (show j < L.length by omega)]
  by_cases h1 : i = j + 1
  · subst h1; simp
  · by_cases h2 : i = j
    · subst h2; simp
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem length_swapAt (j : Nat) (L : List Nat) : (swapAt j L).length = L.length := by
  unfold swapAt; simp

theorem swapAt_eq_map {j : Nat} {L : List Nat} (hnd : L.Nodup) (hj : j + 1 < L.length) :
    swapAt j L = L.map (tswap (L[j]'(by omega)) L[j + 1]) := by
  apply List.ext_getElem
  · rw [length_swapAt, List.length_map]
  · intro i h1 h2
    rw [List.length_map] at h2
    rw [swapAt_getElem hj i h1 h2, List.getElem_map]
    unfold tswap
    have hne : ∀ {a b : Nat} (ha : a < L.length) (hb : b < L.length), L[a] = L[b] → a = b :=
      fun ha hb h => nodup_getElem_inj hnd ha hb h
    by_cases h3 : i = j + 1
    · subst h3
      have : ¬ L[j + 1] = L[j]'(by omega) := fun h => by have := hne h2 (by omega) h; omega
      simp [this]
    · by_cases h4 : i = j
      · subst h4; simp
      · have e1 : ¬ L[i] = L[j]'(by omega) := fun h => h4 (hne h2 (by omega) h)
        have e2 : ¬ L[i] = L[j + 1] := fun h => h3 (hne h2 hj h)
        simp [h3, h4, e1, e2]

theorem swapAt_mem_orders {n j : Nat} (hj : j + 1 < n) {L : List Nat} (hL : L ∈ orders n) :
    swapAt j L ∈ orders n := by
  have hlen := length_of_mem_orders hL
  rw [swapAt_eq_map (nodup_of_mem_orders hL) (by omega)]
  generalize ha : L[j]'(by omega) = a
  generalize hb : L[j + 1]'(by omega) = b
  have hal : a < n := (mem_of_mem_orders hL a).mp (by rw [← ha]; exact List.getElem_mem _)
  have hbl : b < n := (mem_of_mem_orders hL b).mp (by rw [← hb]; exact List.getElem_mem _)
  have hlt : ∀ x, x < n ↔ tswap a b x < n := by
    intro x; unfold tswap
    by_cases h1 : x = a
    · subst h1; simp [hal, hbl]
    · by_cases h2 : x = b
      · subst h2; simp [h1, hal, hbl]
      · simp [h1, h2]
  exact map_mem_orders (fun x => tswap_tswap x) (fun x => tswap_tswap x) hlt hL

/-! ### Features of predicates agreeing on orders -/

theorem card_congr {n : Nat} {p q : List Nat → Bool} (h : ∀ L, L ∈ orders n → p L = q L) :
    card n p = card n q :=
  List.countP_congr (fun L hL => by rw [h L hL])

theorem adjAt_congr {n j : Nat} (hj : j + 1 < n) {p q : List Nat → Bool}
    (h : ∀ L, L ∈ orders n → p L = q L) : adjAt n j p = adjAt n j q :=
  List.countP_congr (fun L hL => by rw [h L hL, h _ (swapAt_mem_orders hj hL)])

theorem adj_congr {n : Nat} {p q : List Nat → Bool} (h : ∀ L, L ∈ orders n → p L = q L) :
    adj n p = adj n q := by
  unfold adj
  congr 1
  apply List.map_congr_left
  intro j hj
  exact adjAt_congr (by have := List.mem_range.mp hj; omega) h

/-! ### The table's counting functions -/

theorem countP_eq_sum_cond {α : Type} (p : α → Bool) : ∀ (l : List α),
    l.countP p = (l.map (fun x => cond (p x) 1 0)).sum
  | [] => rfl
  | x :: l => by
    rw [List.countP_cons, countP_eq_sum_cond p l, List.map_cons, List.sum_cons]
    cases p x <;> simp <;> omega

/-- Positions along a list of orders. -/
def IdxFrom (P : List (List Nat)) (q : Nat) : Prop := P.map lexIdx = List.range' q P.length

theorem idxFrom_tail {L : List Nat} {P : List (List Nat)} {q : Nat} (h : IdxFrom (L :: P) q) :
    lexIdx L = q ∧ IdxFrom P (q + 1) := by
  unfold IdxFrom at h ⊢
  simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at h
  exact h

theorem cardOf_aux (r : Nat) : ∀ (P : List (List Nat)) (f : List Nat → List Nat) (q : Nat), IdxFrom P q →
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun _ _ ih q => Nat.add (cond (Nat.testBit r q) 1 0) (ih (Nat.succ q))) (P.map f)) q =
    (P.map (fun L => cond (memM r L) 1 0)).sum
  | [], _, _, _ => rfl
  | L :: P, f, q, h => by
    obtain ⟨h1, h2⟩ := idxFrom_tail h
    show Nat.add (cond (Nat.testBit r q) 1 0) _ = _
    rw [cardOf_aux r P f (q + 1) h2, List.map_cons, List.sum_cons]
    unfold memM
    rw [h1]
    rfl

theorem countIn_eq (r : Nat) : ∀ (row : List Nat), countIn r row = (row.map (fun t => cond (r.testBit t) 1 0)).sum
  | [] => rfl
  | t :: row => by
    show Nat.add (cond (Nat.testBit r t) 1 0) (countIn r row) = _
    rw [countIn_eq r row, List.map_cons, List.sum_cons]
    rfl

theorem a5Of_aux (r : Nat) : ∀ (P : List (List Nat)) (f : List Nat → List Nat) (q : Nat), IdxFrom P q →
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun row _ ih q => Nat.add (cond (Nat.testBit r q) (countIn r row) 0) (ih (Nat.succ q))) (P.map f)) q =
    (P.map (fun L => cond (memM r L) (countIn r (f L)) 0)).sum
  | [], _, _, _ => rfl
  | L :: P, f, q, h => by
    obtain ⟨h1, h2⟩ := idxFrom_tail h
    show Nat.add (cond (Nat.testBit r q) (countIn r (f L)) 0) _ = _
    rw [a5Of_aux r P f (q + 1) h2, List.map_cons, List.sum_cons]
    unfold memM
    rw [h1]
    rfl

theorem a53Of_aux (r : Nat) : ∀ (P : List (List Nat)) (f : List Nat → Nat) (q : Nat), IdxFrom P q →
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun t _ ih q => Nat.add (cond (Nat.testBit r q) (cond (Nat.testBit r t) 1 0) 0) (ih (Nat.succ q)))
      (P.map f)) q =
    (P.map (fun L => cond (memM r L) (cond (r.testBit (f L)) 1 0) 0)).sum
  | [], _, _, _ => rfl
  | L :: P, f, q, h => by
    obtain ⟨h1, h2⟩ := idxFrom_tail h
    show Nat.add (cond (Nat.testBit r q) (cond (Nat.testBit r (f L)) 1 0) 0) _ = _
    rw [a53Of_aux r P f (q + 1) h2, List.map_cons, List.sum_cons]
    unfold memM
    rw [h1]
    rfl

theorem idxFrom_lexOrders5 : IdxFrom (lexOrders 5) 0 := by
  unfold IdxFrom
  rw [lexIdx_lexOrders5'', List.range_eq_range']

theorem nodup_lexOrders5 : (lexOrders 5).Nodup := by
  have h := lexIdx_lexOrders5''
  have hn : ((lexOrders 5).map lexIdx).Nodup := by rw [h]; exact List.nodup_range
  exact List.Pairwise.of_map lexIdx (fun a b hab heq => hab (heq ▸ rfl)) hn

theorem perm_lexOrders5 : (lexOrders 5).Perm (orders 5) :=
  perm_of_nodup_of_mem_iff' nodup_lexOrders5 (orders_nodup 5) (fun _ => mem_lexOrders)

/-! ### The fields -/

/-- The type index of a five-domain, read from the table. -/
noncomputable def ty5 (p : List Nat → Bool) : Nat := table5.find (m5 p) >>> 154


/-- `D φ` of a five-type: the scaled per-order weight (offset removed). -/
noncomputable def pot5 (k : Nat) : Int := (potT.find k : Int) - 2 ^ 40

theorem ty5_congr {p q : List Nat → Bool} (h : ∀ L, L ∈ orders 5 → p L = q L) : ty5 p = ty5 q := by
  unfold ty5; rw [m5_congr h]

theorem fieldsOK_sound {T potT : KTree} {sw : List (List Nat)} {sw3 : List Nat} {k r : Nat}
    (h : fieldsOK T potT sw sw3 k r = true) :
    T.find r >>> 154 = k ∧ (T.find r >>> 128) % 256 = cardOf sw r ∧
    (T.find r >>> 136) % 1024 = a5Of sw r ∧ (T.find r >>> 146) % 256 = a53Of sw3 r ∧
    T.find r % 2 ^ 64 + cD5 * a5Of sw r + cE * (cardOf sw r + (if k = 866 then 4 else 0)) + cardOf sw r * 2 ^ 40 =
      2 ^ 60 + cK * cardOf sw r + cardOf sw r * potT.find k ∧
    (T.find r >>> 64) % 2 ^ 64 + cardOf sw r * potT.find k + cD5 * a53Of sw3 r + (if k = 41 then 4 * cE else 0) =
      2 ^ 60 + cardOf sw r * 2 ^ 40 := by
  unfold fieldsOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  replace h1 := Nat.eq_of_beq_eq_true h1
  replace h2 := Nat.eq_of_beq_eq_true h2
  replace h3 := Nat.eq_of_beq_eq_true h3
  replace h4 := Nat.eq_of_beq_eq_true h4
  replace h5 := Nat.eq_of_beq_eq_true h5
  replace h6 := Nat.eq_of_beq_eq_true h6
  have e866 : cond (Nat.beq k 866) 4 0 = (if k = 866 then 4 else 0) := by
    by_cases hk : k = 866
    · subst hk; rfl
    · rw [if_neg hk]
      cases h : Nat.beq k 866
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hk
  have e41 : cond (Nat.beq k 41) (Nat.mul 4 cE) 0 = (if k = 41 then 4 * cE else 0) := by
    by_cases hk : k = 41
    · subst hk; rfl
    · rw [if_neg hk]
      cases h : Nat.beq k 41
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hk
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [← e866]
    have : off60 = 2 ^ 60 := off60_eq
    have h40 : off40 = 2 ^ 40 := by decide
    rw [this, h40] at h5
    have hm : (18446744073709551616 : Nat) = 2 ^ 64 := by decide
    rw [hm] at h5
    exact h5
  · rw [← e41]
    have : off60 = 2 ^ 60 := off60_eq
    have h40 : off40 = 2 ^ 40 := by decide
    rw [this, h40] at h6
    have hm : (18446744073709551616 : Nat) = 2 ^ 64 := by decide
    rw [hm] at h6
    exact h6

end CDCert.K6
