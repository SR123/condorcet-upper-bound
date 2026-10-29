/-
CDCert.K6.TabSem — **what the five-table says**, for every nonempty five-label domain of
`groupsEP 5` (from the kernel checks `T2`, `T3`, `CheckAux` and five-level coverage).

* `tabInv`: relabelling invariance of the table (`TabInv`);
* `cardOf_sw5`, `a5Of_sw5`, `a53Of_sw53`: the table's counting functions compute `card`,
  `adj` and `adjAt _ 3` of the representative's domain;
* `ty5`, `pot5`: the type index and the scaled per-order weight `D φ` read from the table;
* `tab_fields`: for a nonempty domain `p`, the table fields are `card 5 p`, `adj 5 p`,
  `adjAt 5 3 p`, the type index is below 1160, and
    `vB5 (m5 p) = K c + c·pot − (D/5)·adj − ηD (c + 4[type 866])`,
    `vT5 (m5 p) = − c·pot − (D/5)·adjAt₃ − 4ηD [type 41]`
  with `c = card 5 p`, `pot = pot5 (ty5 p)`;
* `ty5_relabel`: the type index is invariant under relabelling.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.TabSemA
import CDCert.K6.TabSemB
import CDCert.K6.Tab.T2All
import CDCert.K6.Tab.T3All
import CDCert.K6.Tab.CheckAux

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000

/-- **Relabelling invariance of the five-table.** -/
theorem tabInv : TabInv := tabInv_of_T2 t2_all

theorem cardOf_sw5 (r : Nat) : cardOf sw5 r = card 5 (memM r) := by
  have h := cardOf_aux r (lexOrders 5) (fun L => (List.range 4).map (fun j => lexIdx (swapAt j L))) 0
    idxFrom_lexOrders5
  unfold cardOf
  rw [sw5_eq, h, card, ← perm_lexOrders5.countP_eq, countP_eq_sum_cond]

theorem sum_cond_and {α : Type} (l : List α) (p : α → Bool) (g : α → Nat) :
    (l.map (fun x => cond (p x) (g x) 0)).sum = (l.map (fun x => cond (p x) (g x) 0)).sum := rfl

theorem a5Of_sw5 (r : Nat) : a5Of sw5 r = adj 5 (memM r) := by
  have h := a5Of_aux r (lexOrders 5) (fun L => (List.range 4).map (fun j => lexIdx (swapAt j L))) 0
    idxFrom_lexOrders5
  have e0 : a5Of sw5 r = ((lexOrders 5).map (fun L =>
      cond (memM r L) (countIn r ((List.range 4).map (fun j => lexIdx (swapAt j L)))) 0)).sum := by
    unfold a5Of
    rw [sw5_eq]
    exact h
  have e1 : ∀ L, L ∈ lexOrders 5 → cond (memM r L) (countIn r ((List.range 4).map (fun j => lexIdx (swapAt j L)))) 0 =
      ((List.range 4).map (fun j => cond (memM r L && memM r (swapAt j L)) 1 0)).sum := by
    intro L _
    rw [countIn_eq, List.map_map]
    cases memM r L
    · simp only [cond_false, Bool.false_and]
      induction (List.range 4) with
      | nil => rfl
      | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ← ih]
    · simp only [cond_true, Bool.true_and]
      rfl
  rw [e0, List.map_congr_left e1, sum_comm]
  show _ = ((List.range 4).map (fun j => adjAt 5 j (memM r))).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  unfold adjAt
  rw [← perm_lexOrders5.countP_eq (fun M => memM r M && memM r (swapAt j M)), countP_eq_sum_cond]

theorem a53Of_sw53 (r : Nat) : a53Of sw53 r = adjAt 5 3 (memM r) := by
  have h := a53Of_aux r (lexOrders 5) (fun L => lexIdx (swapAt 3 L)) 0 idxFrom_lexOrders5
  have e0 : a53Of sw53 r = ((lexOrders 5).map (fun L =>
      cond (memM r L) (cond (r.testBit (lexIdx (swapAt 3 L))) 1 0) 0)).sum := by
    unfold a53Of
    rw [sw53_eq]
    exact h
  rw [e0]
  unfold adjAt
  rw [← perm_lexOrders5.countP_eq (fun M => memM r M && memM r (swapAt 3 M)), countP_eq_sum_cond]
  apply congrArg List.sum
  apply List.map_congr_left
  intro L _
  show cond (memM r L) (cond (memM r (swapAt 3 L)) 1 0) 0 = cond (memM r L && memM r (swapAt 3 L)) 1 0
  cases memM r L <;> rfl

theorem ty5_relabel {p : List Nat → Bool} (hp : IsDom 5 p) {σ : List Nat} (hσ : σ ∈ orders 5) :
    ty5 (fun L => p (rlab σ L)) = ty5 p := by
  unfold ty5
  rw [tabInv p hp σ hσ]

theorem rep5T_mem {k : Nat} (hk : k < 1160) : rep5T.find k ∈ reps5 := by
  have h := rep5T_eq
  have hl : k < ((List.range 1160).map rep5T.find).length := by simp; exact hk
  have := List.getElem_mem hl
  rw [List.getElem_map, List.getElem_range, h] at this
  exact this

theorem vB_arith (X c a P k : Nat)
    (h : X + cD5 * a + cE * (c + (if k = 866 then 4 else 0)) + c * 2 ^ 40 = 2 ^ 60 + cK * c + c * P) :
    (X : Int) - 2 ^ 60 = (cK : Int) * c + c * ((P : Int) - 2 ^ 40) - cD5 * a -
      cE * (c + (if k = 866 then 4 else 0)) := by
  have hK : cK = 5587021440 := rfl
  have hD : cD5 = 1769223456 := rfl
  have hE : cE = 58198140 := rfl
  rw [hK, hD, hE] at h ⊢
  rw [Int.mul_sub]
  by_cases hk : k = 866
  · rw [if_pos hk] at h ⊢
    have e := congrArg (fun x : Nat => (x : Int)) h
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e
    omega
  · rw [if_neg hk] at h ⊢
    have e := congrArg (fun x : Nat => (x : Int)) h
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e
    omega

theorem vT_arith (X c a P k : Nat)
    (h : X + c * P + cD5 * a + (if k = 41 then 4 * cE else 0) = 2 ^ 60 + c * 2 ^ 40) :
    (X : Int) - 2 ^ 60 = -(c * ((P : Int) - 2 ^ 40)) - cD5 * a - (if k = 41 then 4 * cE else 0) := by
  have hD : cD5 = 1769223456 := rfl
  have hE : cE = 58198140 := rfl
  rw [hD, hE] at h ⊢
  rw [Int.mul_sub]
  by_cases hk : k = 41
  · rw [if_pos hk] at h ⊢
    have e := congrArg (fun x : Nat => (x : Int)) h
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e
    omega
  · rw [if_neg hk] at h ⊢
    have e := congrArg (fun x : Nat => (x : Int)) h
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e
    omega

/-- **The five-table fields, for every nonempty five-domain.** -/
theorem tab_fields {p : List Nat → Bool} (hp : IsDom 5 p) (hne : ¬ IsEmptyOn 5 p) :
    (table5.find (m5 p) >>> 128) % 256 = card 5 p ∧
    (table5.find (m5 p) >>> 136) % 1024 = adj 5 p ∧
    (table5.find (m5 p) >>> 146) % 256 = adjAt 5 3 p ∧
    ty5 p < 1160 ∧
    vB5 (m5 p) = (cK : Int) * card 5 p + card 5 p * pot5 (ty5 p) - cD5 * adj 5 p -
      cE * (card 5 p + (if ty5 p = 866 then 4 else 0)) ∧
    vT5 (m5 p) = -(card 5 p * pot5 (ty5 p)) - cD5 * adjAt 5 3 p - (if ty5 p = 41 then 4 * cE else 0) := by
  -- a nonempty domain is a relabelled representative
  have : ∃ L0, L0 ∈ orders 5 ∧ p L0 = true := by
    apply Classical.byContradiction
    intro hno
    apply hne
    intro L hL
    cases h : p L
    · rfl
    · exact absurd ⟨L, hL, h⟩ hno
  obtain ⟨L0, hL0, hp0⟩ := this
  obtain ⟨c, hc, hpc⟩ := hp
  obtain ⟨ρ, hρ, k, hk, hiso⟩ := five_cover hc hL0 (by rw [← hpc L0 hL0]; exact hp0)
  have hR := rep5T_mem hk
  have hpr : ∀ L, L ∈ orders 5 → p L = memM (rep5T.find k) (rlab ρ L) := fun L hL => (hpc L hL).trans (hiso L hL)
  -- the table value is the representative's
  have hv : table5.find (m5 p) = table5.find (rep5T.find k) := by
    rw [m5_congr hpr, find_relabel_rep t2_all hR hρ]
  have hmr : m5 (memM (rep5T.find k)) = rep5T.find k :=
    maskOf_memM lexIdx_lexOrders5'' (lt_pow_of_mem_reps5 hR)
  -- features of `p` are those of the representative
  have hcard : card 5 p = card 5 (memM (rep5T.find k)) := by
    rw [card_congr hpr, card_relabel hρ]
  have hadj : adj 5 p = adj 5 (memM (rep5T.find k)) := by
    rw [adj_congr hpr, adj_relabel hρ]
  have hadj3 : adjAt 5 3 p = adjAt 5 3 (memM (rep5T.find k)) := by
    rw [adjAt_congr (by omega) hpr, adjAt_relabel (by omega) hρ]
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fieldsOK_sound (t3_all k hk)
  rw [cardOf_sw5] at f2 f5 f6
  rw [a5Of_sw5] at f3 f5
  rw [a53Of_sw53] at f4 f6
  have hty : ty5 p = k := by unfold ty5; rw [hv, f1]
  have hne0 : m5 p ≠ 0 := fun h0 => hne ((m5_eq_zero_iff p).mp h0)
  refine ⟨by rw [hv, f2, hcard], by rw [hv, f3, hadj], by rw [hv, f4, hadj3], by rw [hty]; exact hk, ?_, ?_⟩
  · unfold vB5
    rw [if_neg hne0, hv, hty, hcard, hadj]
    unfold pot5
    exact vB_arith _ _ _ _ k f5
  · unfold vT5
    rw [if_neg hne0, hv, hty, hcard, hadj3]
    unfold pot5
    exact vT_arith _ _ _ _ k f6

end CDCert.K6
