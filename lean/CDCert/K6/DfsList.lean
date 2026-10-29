/-
CDCert.K6.DfsList — the memoized DFS over mask groups, read off at list level.

* `andAll_maskOf`: the AND of the masks of a choice with the mask of `P` is the mask
  of `P ∧ allows`;
* `dfs_sound_list`: if `dfs1 leafOK` passes on the pre-shifted masks over `base` of
  list-level groups `G`, started at the mask of `P`, then for every choice `cl` of
  `G` whose solution set within `P` meets `base`, `leafOK` holds at the final state,
  whose decoded value is the mask of `P ∧ allows cl`;
* `memM`, `maskOf_memM`, `testBit_maskOf_memM`: membership read from a mask via
  `lexIdx`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Sound
import CDCert.K6.MaskSem

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

theorem andAll_maskOf (base : List (List Nat)) :
    ∀ (P : List Nat → Bool) (cl : List (Opt (List Nat))),
      andAll (maskOf base P) (cl.map (fun o => maskOf base o)) =
        maskOf base (fun L => P L && allows cl L)
  | P, [] => by
    show maskOf base P = _
    congr 1
    funext L
    simp [allows]
  | P, o :: cl => by
    show andAll (maskOf base P &&& maskOf base o) (cl.map (fun o => maskOf base o)) = _
    rw [maskOf_and, andAll_maskOf base _ cl]
    congr 1
    funext L
    rw [allows_cons, Bool.and_assoc]

theorem maskOf_ne_zero {base : List (List Nat)} {P : List Nat → Bool} {L : List Nat}
    (hL : L ∈ base) (hP : P L = true) : maskOf base P ≠ 0 := by
  intro h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have := testBit_maskOf base P i
  rw [h, Nat.zero_testBit, List.getElem?_eq_getElem hi] at this
  simp only at this
  rw [hP] at this
  cases this

/-- **DFS soundness at list level.** -/
theorem dfs_sound_list (leafOK : Nat → Bool) (base : List (List Nat)) (G : List (Group (List Nat)))
    (P : List Nat → Bool)
    (h : dfs1 leafOK (G.map (fun g => g.map (fun o => maskOf base o <<< 64))) (enc (maskOf base P)) = true)
    (cl : List (Opt (List Nat))) (hc : IsChoice cl G)
    (hne : ∃ L, L ∈ base ∧ P L = true ∧ allows cl L = true) :
    ∃ e, leafOK e = true ∧ e >>> 64 = maskOf base (fun L => P L && allows cl L) := by
  have hc' : IsChoice ((cl.map (fun o => maskOf base o)).map (· <<< 64))
      (G.map (fun g => g.map (fun o => maskOf base o <<< 64))) := by
    have h1 := hc.map (fun o => maskOf base o <<< 64)
    rw [List.map_map]
    exact h1
  have hdec : runE (enc (maskOf base P)) ((cl.map (fun o => maskOf base o)).map (· <<< 64)) >>> 64 =
      maskOf base (fun L => P L && allows cl L) := by
    rw [shiftRight_runE, shiftRight_enc, andAll_maskOf]
  refine ⟨_, dfs1_sound leafOK _ _ h _ hc' ?_, hdec⟩
  intro hz
  have : runE (enc (maskOf base P)) ((cl.map (fun o => maskOf base o)).map (· <<< 64)) >>> 64 = 0 := by
    rw [hz]; rfl
  rw [hdec] at this
  obtain ⟨L, hL, hP, ha⟩ := hne
  exact maskOf_ne_zero hL (show (P L && allows cl L) = true by rw [hP, ha]; rfl) this

/-! ### Membership read from a mask -/

/-- `L` is in the domain with mask `r` (indexed by `lexIdx`). -/
def memM (r : Nat) (L : List Nat) : Bool := r.testBit (lexIdx L)

theorem testBit_maskOf_memM {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    (r i : Nat) (hi : i < P.length) : (maskOf P (memM r)).testBit i = r.testBit i := by
  rw [testBit_maskOf, List.getElem?_eq_getElem hi]
  simp only [memM]
  rw [lexIdx_getElem hP i hi]

theorem maskOf_memM {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length) {r : Nat}
    (hr : r < 2 ^ P.length) : maskOf P (memM r) = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < P.length
  · exact testBit_maskOf_memM hP r i hi
  · have h1 : (maskOf P (memM r)).testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (maskOf_lt P _) (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : r.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

/-- Masks over `P` agree iff the predicates agree on `P`. -/
theorem maskOf_eq_iff (P : List (List Nat)) (p q : List Nat → Bool) :
    maskOf P p = maskOf P q ↔ ∀ L, L ∈ P → p L = q L := by
  constructor
  · intro h L hL
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
    have := congrArg (fun m => Nat.testBit m i) h
    simp only [testBit_maskOf, List.getElem?_eq_getElem hi] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_maskOf, testBit_maskOf]
    cases hi : P[i]? with
    | none => rfl
    | some L => exact h L (List.mem_of_getElem? hi)

/-- **Lifts.** If `lifts` lists, for each `q ∈ P`, the mask over `base` of the orders
projecting to `q`, then `liftOf lifts r` is the mask of the orders whose projection is
in the domain with mask `r`. -/
theorem liftOf_maskOf {base P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    (proj : List Nat → List Nat) (hproj : ∀ L, L ∈ base → proj L ∈ P) (r : Nat) :
    liftOf (P.map (fun q => maskOf base (fun L => proj L == q))) r =
      maskOf base (fun L => memM r (proj L)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [testBit_liftOf, testBit_maskOf]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rw [List.length_map] at hj
    rw [List.getElem_map, testBit_maskOf] at h2
    cases hi : base[i]? with
    | none => rw [hi] at h2; cases h2
    | some L =>
      rw [hi] at h2
      simp only [beq_iff_eq] at h2
      show memM r (proj L) = true
      unfold memM
      rw [h2, lexIdx_getElem hP j hj]
      exact h1
  · intro h
    cases hi : base[i]? with
    | none => rw [hi] at h; cases h
    | some L =>
      rw [hi] at h
      have hLb : L ∈ base := List.mem_of_getElem? hi
      obtain ⟨hlt, heq⟩ := getElem_lexIdx hP (hproj L hLb)
      refine ⟨lexIdx (proj L), by rw [List.length_map]; exact hlt, h, ?_⟩
      rw [List.getElem_map, testBit_maskOf, hi]
      simp only [beq_iff_eq]
      exact heq.symm

/-- Reading an equality of masks over `P` with a mask `r` member by member. -/
theorem memM_of_maskOf_eq {P : List (List Nat)} (hP : P.map lexIdx = List.range P.length)
    {p : List Nat → Bool} {r : Nat} (h : maskOf P p = r) {L : List Nat} (hL : L ∈ P) :
    p L = memM r L := by
  obtain ⟨hlt, heq⟩ := getElem_lexIdx hP hL
  have := congrArg (fun m => Nat.testBit m (lexIdx L)) h
  simp only [testBit_maskOf, List.getElem?_eq_getElem hlt, heq] at this
  exact this

end CDCert.K6
