/-
CDCert.BridgeK6 — **the density bound for Codex's actual domains**: every `D ∈ InF` on `n + 1`
alternatives satisfies

  `InF.density : 3 (n + 1) |D| ≤ 8 · deletionSum D`

(Proposition `prop:density`, `del(K) ≥ 3n|K|/8`). The list-level theorem `CDCert.K6.adj_le`
(`8 A(K) ≤ 5 n |K|` for every `groupsEP n` domain, from the finite lemma by windows, telescoping and
ordered concatenation) is transported to Codex's `adjacencyCount` through `toList`, and combined with
Codex's fibre identity `deletionSum + gapCount + adjacencyCount = (n + 1) |D|` and `gapCount = 0` on
`InF`.

* `getElem_toList`: the `i`-th entry of `toList r` is the alternative of rank `i`;
* `toList_swapLetter`: the letter `j` swaps the entries `j`, `j + 1` of the list;
* `card_predOf`, `adjacencyCount_eq_adj`: `|D|` and `A(D)` are the list-level `card` and `adj` of the
  predicate `predOf D`; `isDom_predOf`: for `D ∈ InF` it is a `groupsEP` domain.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0 + Mathlib v4.26.0. No `sorry`, no custom axioms, no `native_decide`.
-/
import Condorcet.NoGaps
import Condorcet.Letters
import Condorcet.DirectedAdjacency
import CDCert.BridgeEP
import CDCert.K6.Density

namespace CDCert.Bridge

open Condorcet CDCert CDCert.Examples CDCert.ListOrder

/-! ### Entries of `toList` -/

theorem before_getElem_iff {L : List Nat} (hnd : L.Nodup) :
    ∀ {i : Nat} (hi : i < L.length) (b : Nat), before b L[i] L = true ↔ b ∈ L.take i := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons y L ih =>
    intro i hi b
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, List.not_mem_nil, iff_false]
      rw [before_cons]
      by_cases hyb : y = b
      · rw [if_pos hyb]
        simpa using hnd'.1
      · rw [if_neg hyb, if_pos rfl]
        simp
    | succ i =>
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.mem_cons]
      have hi' : i < L.length := by simpa using hi
      have hne : y ≠ L[i] := fun h => hnd'.1 (h ▸ List.getElem_mem hi')
      rw [before_cons]
      by_cases hyb : y = b
      · rw [if_pos hyb]
        simp only [decide_eq_true_eq]
        exact ⟨fun _ => Or.inl hyb.symm, fun _ => List.getElem_mem hi'⟩
      · rw [if_neg hyb, if_neg hne, ih hnd'.2 hi' b]
        constructor
        · exact Or.inr
        · rintro (h | h)
          · exact absurd h.symm hyb
          · exact h

/-- The alternatives above `L[i]` in a list are its first `i` entries. -/
theorem card_above_toList {n : Nat} (r : Condorcet.Order (Fin n)) {i : Nat} (hi : i < (toList r).length) :
    (Finset.univ.filter (fun b : Fin n => r b ⟨(toList r)[i], (mem_of_mem_orders (toList_mem r) _).mp
      (List.getElem_mem hi)⟩ = true)).card = i := by
  classical
  have hnd := nodup_of_mem_orders (toList_mem r)
  set x : Fin n := ⟨(toList r)[i], (mem_of_mem_orders (toList_mem r) _).mp (List.getElem_mem hi)⟩ with hx
  have hset : (Finset.univ.filter (fun b : Fin n => r b x = true)).map Fin.valEmbedding =
      ((toList r).take i).toFinset := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← before_toList r b x] at hb
      exact (before_getElem_iff hnd hi b.val).mp hb
    · intro hv
      have hvL : v ∈ toList r := List.mem_of_mem_take hv
      have hvn : v < n := (mem_of_mem_orders (toList_mem r) v).mp hvL
      refine ⟨⟨v, hvn⟩, ?_, rfl⟩
      rw [← before_toList r ⟨v, hvn⟩ x]
      exact (before_getElem_iff hnd hi v).mpr hv
  have := congrArg Finset.card hset
  rw [Finset.card_map, List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup hnd), List.length_take] at this
  rw [this]
  omega

/-- **The `i`-th entry of `toList r` is the alternative of rank `i`.** -/
theorem getElem_toList {n : Nat} (r : Condorcet.Order (Fin (n + 1))) {i : Nat} (hi : i < (toList r).length) :
    (toList r)[i] = (r.atPos ⟨i, by rw [CDCert.K6.length_of_mem_orders (toList_mem r)] at hi; exact hi⟩).val := by
  classical
  have hlt : (toList r)[i] < n + 1 := (mem_of_mem_orders (toList_mem r) _).mp (List.getElem_mem hi)
  have hrank : r.rank ⟨(toList r)[i], hlt⟩ = i := by
    have hc := card_above_toList r hi
    have e : r.above ⟨(toList r)[i], hlt⟩ =
        Finset.univ.filter (fun b : Fin (n + 1) => r b ⟨(toList r)[i], hlt⟩ = true) := by
      ext b; simp
    unfold Condorcet.Order.rank
    rw [e]
    exact hc
  have h1 : r.rank (r.atPos ⟨i, by rw [CDCert.K6.length_of_mem_orders (toList_mem r)] at hi; exact hi⟩) = i :=
    r.rank_atPos _
  have := r.rank_injective (hrank.trans h1.symm)
  exact congrArg Fin.val this

/-! ### Letters are list swaps -/

theorem getElem_swapAt' {M : List Nat} {j k : Nat} (hj : j + 1 < M.length) (hk : k < M.length) :
    (CDCert.K6.swapAt j M)[k]'(by unfold CDCert.K6.swapAt; simpa using hk) =
      if k = j then M[j + 1] else if k = j + 1 then M[j] else M[k] := by
  unfold CDCert.K6.swapAt
  rw [List.getElem_set, List.getElem_set]
  have e1 : M.getD j 0 = M[j] := CDCert.K6.getD_of_lt (by omega)
  have e2 : M.getD (j + 1) 0 = M[j + 1] := CDCert.K6.getD_of_lt hj
  simp only [e1, e2]
  by_cases h1 : k = j
  · subst h1; simp
  · by_cases h2 : k = j + 1
    · subst h2; simp
    · rw [if_neg (fun h => h2 h.symm), if_neg (fun h => h1 h.symm), if_neg h1, if_neg h2]

/-- Relabelling a natural label by the inverse of a transposition (any decidability instance). -/
theorem relabelNat_swap_symm {m : Nat} {inst : DecidableEq (Fin m)} (p q : Fin m) (x : Nat) (hx : x < m) :
    relabelNat (@Equiv.swap (Fin m) inst p q).symm x =
      if x = p.val then q.val else if x = q.val then p.val else x := by
  unfold relabelNat
  rw [dif_pos hx, Equiv.symm_swap, Equiv.swap_apply_def]
  by_cases h1 : x = p.val
  · rw [if_pos (Fin.ext h1), if_pos h1]
  · rw [if_neg (fun h => h1 (congrArg Fin.val h)), if_neg h1]
    by_cases h2 : x = q.val
    · rw [if_pos (Fin.ext h2), if_pos h2]
    · rw [if_neg (fun h => h2 (congrArg Fin.val h)), if_neg h2]

/-- **The letter `j` of an order swaps the entries `j`, `j + 1` of its list.** -/
theorem toList_swapLetter {n : Nat} (r : Condorcet.Order (Fin (n + 1))) (j : Fin n) :
    toList (swapLetter r j) = CDCert.K6.swapAt j.val (toList r) := by
  have hlen : (toList r).length = n + 1 := CDCert.K6.length_of_mem_orders (toList_mem r)
  have hnd := nodup_of_mem_orders (toList_mem r)
  have hp : (toList r)[j.val]'(by omega) = (r.atPos j.castSucc).val := getElem_toList r _
  have hq : (toList r)[j.val + 1]'(by omega) = (r.atPos j.succ).val := getElem_toList r _
  unfold swapLetter Condorcet.Order.swapLabels
  rw [toList_restrict_perm]
  apply List.ext_getElem
  · unfold CDCert.K6.swapAt; simp
  · intro k h1 h2
    have hk : k < (toList r).length := by simpa using h1
    have hx : (toList r)[k] < n + 1 := (mem_of_mem_orders (toList_mem r) _).mp (List.getElem_mem hk)
    rw [List.getElem_map, getElem_swapAt' (by omega) hk, relabelNat_swap_symm _ _ _ hx, ← hp, ← hq]
    have hjk : ((toList r)[k] = (toList r)[j.val]'(by omega)) ↔ k = j.val := hnd.getElem_inj_iff
    have hjk' : ((toList r)[k] = (toList r)[j.val + 1]'(by omega)) ↔ k = j.val + 1 := hnd.getElem_inj_iff
    by_cases e1 : k = j.val
    · rw [if_pos (hjk.mpr e1), if_pos e1]
    · rw [if_neg (fun h => e1 (hjk.mp h)), if_neg e1]
      by_cases e2 : k = j.val + 1
      · rw [if_pos (hjk'.mpr e2), if_pos e2]
      · rw [if_neg (fun h => e2 (hjk'.mp h)), if_neg e2]

/-! ### Counting through `toList` -/

/-- **Counting transfer.** A finset of orders cut out by a predicate that matches a Boolean
predicate on lists has the size of the list count over `orders n`. -/
theorem card_filter_eq_countP {n : Nat} (P : Condorcet.Order (Fin n) → Prop) [DecidablePred P]
    (p : List Nat → Bool) (hP : ∀ r, P r ↔ p (toList r) = true) :
    (Finset.univ.filter P).card = (orders n).countP p := by
  classical
  have hnd : ((orders n).filter p).Nodup := (orders_nodup n).filter p
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnd]
  apply Finset.card_bij (fun r _ => toList r)
  · intro r hr
    rw [List.mem_toFinset, List.mem_filter]
    rw [Finset.mem_filter] at hr
    exact ⟨toList_mem r, (hP r).mp hr.2⟩
  · intro r₁ _ r₂ _ h
    exact toList_injective h
  · intro L hL
    rw [List.mem_toFinset, List.mem_filter] at hL
    refine ⟨ofList L hL.1, ?_, toList_ofList L hL.1⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (hP _).mpr ?_⟩
    rw [toList_ofList]
    exact hL.2

theorem sum_fin_eq_list_range (f : Nat → Nat) : ∀ n : Nat,
    ∑ j : Fin n, f j.val = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Fin.sum_univ_eq_sum_range (fun j => f j) (n + 1), Finset.sum_range_succ,
      ← Fin.sum_univ_eq_sum_range (fun j => f j) n, sum_fin_eq_list_range f n, List.range_succ,
      List.map_append, List.sum_append]
    simp

/-- **`|D|` and `A(D)` are the list-level `card` and `adj`** of the predicate `allows c`, for any
choice `c` whose solution set is `D` through `toList`. -/
theorem card_adj_of_choice {n : Nat} {D : Domain (Fin (n + 1))} {c : List (Opt (List Nat))}
    (hmem : ∀ r, r ∈ D ↔ toList r ∈ domainOf (orders (n + 1)) c) :
    D.card = CDCert.K6.card (n + 1) (allows c) ∧
      adjacencyCount D = CDCert.K6.adj (n + 1) (allows c) := by
  classical
  have hD : ∀ r, r ∈ D ↔ allows c (toList r) = true := by
    intro r
    rw [hmem, mem_domainOf, allows_eq_true]
    exact ⟨fun h => h.2, fun h => ⟨toList_mem r, h⟩⟩
  refine ⟨?_, ?_⟩
  · rw [← Finset.filter_univ_mem D]
    exact card_filter_eq_countP (· ∈ D) (allows c) hD
  · rw [adjacencyCount_eq_letters, Finset.sum_comm]
    unfold CDCert.K6.adj
    rw [Nat.add_sub_cancel, ← sum_fin_eq_list_range (fun j => CDCert.K6.adjAt (n + 1) j (allows c)) n]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.card_filter]
    have e : D.filter (fun r => swapLetter r j ∈ D) =
        Finset.univ.filter (fun r => r ∈ D ∧ swapLetter r j ∈ D) := by
      ext r; simp
    rw [e]
    unfold CDCert.K6.adjAt
    apply card_filter_eq_countP
    intro r
    rw [Bool.and_eq_true, ← hD, ← toList_swapLetter, ← hD]

/-- **Proposition `prop:density`**: every domain of `InF` on `n + 1` alternatives satisfies
`del(D) ≥ 3 (n + 1) |D| / 8`. -/
theorem InF.density {n : Nat} {D : Domain (Fin (n + 1))} (hD : InF D) :
    3 * (n + 1) * D.card ≤ 8 * deletionSum D := by
  obtain ⟨c, hc, hmem, -, -⟩ := InF.toList_domain hD
  obtain ⟨hcard, hadj⟩ := card_adj_of_choice hmem
  have hdom : CDCert.K6.IsDom (n + 1) (allows c) := ⟨c, hc, fun _ _ => rfl⟩
  have hA := CDCert.K6.adj_le hdom
  have hid := deletion_gap_adjacency_identity D
  rw [hD.2.gapCount_zero] at hid
  rw [← hcard, ← hadj, Nat.mul_assoc] at hA
  rw [Nat.mul_assoc]
  omega

end CDCert.Bridge
