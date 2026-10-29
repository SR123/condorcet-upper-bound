/-
CDCert.K6.FamSem — **what the DFS check of a seven-level seed family says**: if a seven-domain `J`
has the seed as the six-slice in the seed block of a copy (`copy1`: the bottom slice `B_6 J`; `copy3`:
the top slice `T_6 J`), then its mask over that copy is a key of the family's tree of final states.

* `pickD`: the options of `groupsD7` chosen by laws `lawN` and pairs `pairN` (one per group);
  `isChoice_pickD`, `all_pickD`: it is a choice for `groupsD7` with the solution set of
  `choiceEPN lawN pairN 7`;
* `stepEnc_shift_eq`, `runE_map_encS`: an encoded run of pre-shifted options is `encS` of the AND;
* **`fam_find`**: from `dfsP (leafF F) (wp fam fullcE (badMask 4320 seed)) (enc fullc) = true`
  for the family `fam = ord.map (fun g => (ocG.getD g []).filter (seedOK seed))` (`ord` a
  permutation of the 56 groups, `ocG` the option masks over the copy): `F.find (maskOf base J) ≠ 0`.
  The run of `J`'s options is a choice of the family (each chosen option contains `J`, hence the
  seed); its final state is `encS (maskOf base J)`; it meets no order of the seed block outside the
  seed; so `dfsP_sound` applies.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.OptSem
import CDCert.K6.Leaf7Sem
import CDCert.K6.DfsPSem
import CDCert.K6.ChoiceN
import CDCert.K6.AllNat

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false

/-! ### The options chosen by a seven-domain -/

/-- The option of a pair group chosen by an optional comparison. -/
def pairD (a b : Nat) : Option Bool → OptD
  | none => .top
  | some true => .pr a b
  | some false => .pr b a

theorem toOpt_pairD (a b : Nat) : ∀ o, (pairD a b o).toOpt = pairChoice a b o
  | none => rfl
  | some true => rfl
  | some false => rfl

theorem pairD_mem (a b : Nat) : ∀ o, pairD a b o ∈ [OptD.top, OptD.pr a b, OptD.pr b a]
  | none => List.mem_cons_self
  | some true => List.mem_cons_of_mem _ List.mem_cons_self
  | some false => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The options of `groupsD7` chosen by laws and pairs. -/
def pickD (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool) : List OptD :=
  (triplesN 7).map (fun t => OptD.law t.1 t.2.1 t.2.2 (lawN t)) ++
    (pairsN 7).map (fun ab => pairD ab.1 ab.2 (pairN ab.1 ab.2))

theorem isChoice_pickD {lawN : Nat × Nat × Nat → Fin 3 × Fin 3} (hlaw : ∀ t, lawN t ∈ lawsExtreme)
    (pairN : Nat → Nat → Option Bool) : IsChoice (pickD lawN pairN) groupsD7 :=
  isChoice_append.mpr ⟨_, _, rfl,
    isChoice_map_map _ _ _ (fun t _ => List.mem_map_of_mem (hlaw t)),
    isChoice_map_map _ _ _ (fun ab _ => pairD_mem ab.1 ab.2 _)⟩

theorem all_pickD (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool) (x : List Nat) :
    (pickD lawN pairN).all (fun d => d.toOpt x) = allows (choiceEPN lawN pairN 7) x := by
  apply Bool.eq_iff_iff.mpr
  rw [allows_choiceEPN, List.all_eq_true]
  unfold pickD
  constructor
  · intro h
    refine ⟨fun t ht => h _ (List.mem_append_left _ (List.mem_map_of_mem ht)), fun a c hac hc => ?_⟩
    have := h _ (List.mem_append_right _ (List.mem_map_of_mem ((mem_pairsN (n := 7) (ab := (a, c))).mpr ⟨hac, hc⟩)))
    rw [toOpt_pairD] at this
    exact this
  · rintro ⟨h1, h2⟩ d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
      exact h1 t ht
    · obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hd
      rw [toOpt_pairD]
      exact h2 ab.1 ab.2 (mem_pairsN.mp hab).1 (mem_pairsN.mp hab).2

theorem length_groupsD7 : groupsD7.length = 56 := rfl

/-! ### Lists -/

theorem getD_eq_getElem' {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_map_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (l : List (List α)) (i : Nat) :
    (l.map f).getD i [] = f (l.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hf.symm
  | some x => rfl

theorem isChoice_getD {α : Type} {c : List α} {gs : List (List α)} (h : IsChoice c gs) (d : α) :
    ∀ i, i < gs.length → c.getD i d ∈ gs.getD i [] := by
  induction h with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons ho _ ih =>
    intro i hi
    cases i with
    | zero => exact ho
    | succ i => exact ih i (by simp only [List.length_cons] at hi; omega)

theorem all_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) (p : Nat → Bool) : l₁.all p = l₂.all p := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  exact ⟨fun h1 x hx => h1 x (h.mem_iff.mpr hx), fun h1 x hx => h1 x (h.mem_iff.mp hx)⟩

theorem all_range_getD {α : Type} (l : List α) (d : α) (p : α → Bool) :
    (List.range l.length).all (fun i => p (l.getD i d)) = l.all p := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have := h i (List.mem_range.mpr hi)
    rw [getD_eq_getElem' d hi] at this
    exact this
  · intro h i hi
    rw [getD_eq_getElem' d (List.mem_range.mp hi)]
    exact h _ (List.getElem_mem _)

/-! ### Encoded runs of pre-shifted options -/

theorem testBit_andAll (i : Nat) : ∀ (c : List Nat) (s : Nat),
    (andAll s c).testBit i = (s.testBit i && c.all (fun o => o.testBit i))
  | [], s => by simp [andAll]
  | o :: c, s => by
    show (andAll (s &&& o) c).testBit i = _
    rw [testBit_andAll i c, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem stepEnc_shift_eq (e o : Nat) : stepEnc e (o <<< 64) = encS ((e >>> 64) &&& o) := by
  have hy : e &&& (o <<< 64) = ((e >>> 64) &&& o) <<< 64 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases h : 64 ≤ i
    · rw [decide_eq_true h, Bool.true_and, Bool.true_and, Nat.add_sub_cancel' h]
    · rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.and_false]
  rw [stepEnc_eq, hy]
  rfl

theorem runE_map_encS : ∀ (c : List Nat) (e : Nat), c ≠ [] → runE e (c.map (· <<< 64)) = encS (andAll (e >>> 64) c)
  | [], _, h => absurd rfl h
  | [o], e, _ => by
    show stepEnc e (o <<< 64) = encS (andAll ((e >>> 64) &&& o) [])
    exact (stepEnc_shift_eq e o).trans rfl
  | o :: o' :: c, e, _ => by
    show runE (stepEnc e (o <<< 64)) ((o' :: c).map (· <<< 64)) = encS (andAll ((e >>> 64) &&& o) (o' :: c))
    rw [runE_map_encS (o' :: c) _ (List.cons_ne_nil _ _), shiftRight_stepEnc]

theorem testBit_encS_high (x : Nat) {i : Nat} (hi : 64 ≤ i) : (encS x).testBit i = x.testBit (i - 64) := by
  unfold encS
  rw [lor_eq', Nat.testBit_or, shiftLeft_eq'', mod_eq', Nat.testBit_shiftLeft, decide_eq_true hi,
    Bool.true_and, testBit_small (mod_hashP_lt _) hi, Bool.or_false]

theorem encS_ne_zero {x : Nat} (h : x ≠ 0) : encS x ≠ 0 := by
  intro h0
  apply h
  rw [← shiftRight_encS x, h0]
  rfl

theorem fullc_eq : fullc = 2 ^ 5040 - 1 := by
  show Nat.sub (Nat.shiftLeft 1 5040) 1 = 2 ^ 5040 - 1
  rw [shiftLeft_eq'', Nat.shiftLeft_eq, Nat.one_mul, Nat.sub_eq]

theorem m720'_eq : m720' = 2 ^ 720 - 1 := by
  show Nat.sub (Nat.shiftLeft 1 720) 1 = 2 ^ 720 - 1
  rw [shiftLeft_eq'', Nat.shiftLeft_eq, Nat.one_mul, Nat.sub_eq]

theorem testBit_badMask (seed i : Nat) :
    (badMask 4320 seed).testBit i = (decide (4384 ≤ i) && (decide (i - 4384 < 720) ^^ seed.testBit (i - 4384))) := by
  show (Nat.shiftLeft (Nat.xor m720' seed) (Nat.add 4320 64)).testBit i = _
  rw [shiftLeft_eq'', Nat.testBit_shiftLeft, show Nat.add 4320 64 = 4384 from rfl, m720'_eq]
  show (decide (i ≥ 4384) && ((2 ^ 720 - 1) ^^^ seed).testBit (i - 4384)) = _
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]

/-! ### Masks -/

theorem testBit_maskOf_imp {base : List (List Nat)} {P Q : List Nat → Bool}
    (h : ∀ x, x ∈ base → P x = true → Q x = true) {i : Nat} (hi : (maskOf base P).testBit i = true) :
    (maskOf base Q).testBit i = true := by
  rw [testBit_maskOf] at hi ⊢
  cases hx : base[i]? with
  | none => rw [hx] at hi; cases hi
  | some x =>
    rw [hx] at hi
    exact h x (List.mem_of_getElem? hx) hi

theorem testBit_maskOf_lt {base : List (List Nat)} (P : List Nat → Bool) {i : Nat} (hi : i < base.length) :
    (maskOf base P).testBit i = P base[i] := by
  rw [testBit_maskOf, List.getElem?_eq_getElem hi]

theorem testBit_maskOf_ge {base : List (List Nat)} (P : List Nat → Bool) {i : Nat} (hi : base.length ≤ i) :
    (maskOf base P).testBit i = false := by
  rw [testBit_maskOf, List.getElem?_eq_none hi]

/-! ### Leaves over chunks -/

theorem allNat_flatten_cons (p : Nat → Bool) (l : List Nat) (ls : List (List Nat)) :
    allNat p (List.flatten (l :: ls)) = (allNat p l && allNat p (List.flatten ls)) := by
  rw [List.flatten_cons, allNat_append']

theorem allNat_flatten_nil (p : Nat → Bool) : allNat p (List.flatten []) = true := rfl

/-! ### A seed family -/

/-- **The DFS check of a seed family, read off**: a seven-domain whose six-slice in the seed block of
the copy `base` is the seed has its mask over `base` as a key of the tree `F` of final states. -/
theorem fam_find (base : List (List Nat)) (hbase : ∀ x, x ∈ base → x ∈ orders 7) (hlen : base.length = 5040)
    (mk : OptD → Nat) (hmk : ∀ d, mk d = Nat.shiftLeft (maskOf base d.toOpt) 64)
    (ocG : List (List Nat)) (hoc : ocG = groupsD7.map (fun g => g.map mk))
    (ord : List Nat) (hord : ord.Perm (List.range 56)) (seed : Nat) (F : KTree)
    (hdfs : dfsP (leafF F) (wp (ord.map (fun g => (ocG.getD g []).filter (seedOK seed))) fullcE
      (badMask 4320 seed)) (enc fullc) = true)
    {J : List Nat → Bool} (hJ : IsDom 7 J) (hblk : ((maskOf base J) >>> 4320) % 2 ^ 720 = seed)
    (hne : seed ≠ 0) : F.find (maskOf base J) ≠ 0 := by
  obtain ⟨c, hc, hJc⟩ := hJ
  obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff 7 c hc
  have hch : IsChoice (pickD lawN pairN) groupsD7 := isChoice_pickD hlaw pairN
  have hchlen : (pickD lawN pairN).length = 56 := by rw [hch.length_eq]; rfl
  have hJx : ∀ x, x ∈ orders 7 → J x = (pickD lawN pairN).all (fun d => d.toOpt x) := fun x hx => by
    rw [hJc x hx, all_pickD]
  have hsub : ∀ g, g < 56 → ∀ x, x ∈ orders 7 → J x = true → ((pickD lawN pairN).getD g .top).toOpt x = true := by
    intro g hg x hx hJ1
    rw [hJx x hx, List.all_eq_true] at hJ1
    apply hJ1
    rw [getD_eq_getElem' _ (by rw [hchlen]; exact hg)]
    exact List.getElem_mem _
  have hmem : ∀ g, g ∈ ord → g < 56 := fun g hg => List.mem_range.mp (hord.mem_iff.mp hg)
  -- the seed is inside `J`'s slice, so every chosen option keeps it
  have hseedbit : ∀ i, seed.testBit i = true → i < 720 ∧ (maskOf base J).testBit (4320 + i) = true := by
    intro i hi
    rw [← hblk, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_iff] at hi
    exact hi
  have hseedOK : ∀ g, g < 56 → seedOK seed (mk ((pickD lawN pairN).getD g .top)) = true := by
    intro g hg
    have heq : Nat.land (Nat.shiftRight (mk ((pickD lawN pairN).getD g .top)) 4384) seed = seed := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [land_eq', shiftRight_eq'', Nat.testBit_and, hmk, shiftLeft_eq'', Nat.testBit_shiftRight,
        Nat.testBit_shiftLeft, decide_eq_true (by omega : 4384 + i ≥ 64), Bool.true_and,
        show 4384 + i - 64 = 4320 + i by omega]
      cases hs : seed.testBit i
      · rw [Bool.and_false]
      · rw [Bool.and_true]
        exact testBit_maskOf_imp (fun x hx hJ1 => hsub g hg x (hbase x hx) hJ1) (hseedbit i hs).2
    unfold seedOK
    rw [heq]
    exact Nat.beq_refl seed
  -- the family choice of `J`
  have hIC : IsChoice (ord.map (fun g => mk ((pickD lawN pairN).getD g .top)))
      (ord.map (fun g => (ocG.getD g []).filter (seedOK seed))) := by
    apply isChoice_map_map
    intro g hg
    rw [List.mem_filter]
    refine ⟨?_, hseedOK g (hmem g hg)⟩
    rw [hoc, getD_map_nil (fun g => g.map mk) rfl]
    exact List.mem_map_of_mem (isChoice_getD hch .top g (by rw [length_groupsD7]; exact hmem g hg))
  have hcF : ord.map (fun g => mk ((pickD lawN pairN).getD g .top)) =
      (ord.map (fun g => maskOf base ((pickD lawN pairN).getD g .top).toOpt)).map (· <<< 64) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro g _
    rw [hmk]
    rfl
  -- the decoded final state is the mask of `J`
  have hdec : andAll fullc (ord.map (fun g => maskOf base ((pickD lawN pairN).getD g .top).toOpt)) =
      maskOf base J := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_andAll, fullc_eq, Nat.testBit_two_pow_sub_one, List.all_map]
    by_cases hj : j < 5040
    · rw [decide_eq_true hj, Bool.true_and, testBit_maskOf_lt _ (by rw [hlen]; exact hj)]
      have hx := hbase _ (List.getElem_mem (by rw [hlen]; exact hj))
      rw [hJx _ hx, all_perm hord, ← hchlen, ← all_range_getD (pickD lawN pairN) .top]
      congr 1
      funext g
      show (maskOf base ((pickD lawN pairN).getD g .top).toOpt).testBit j = _
      rw [testBit_maskOf_lt _ (by rw [hlen]; exact hj)]
    · rw [decide_eq_false hj, Bool.false_and, testBit_maskOf_ge _ (by rw [hlen]; omega)]
  have hne0 : ord.map (fun g => maskOf base ((pickD lawN pairN).getD g .top).toOpt) ≠ [] := by
    intro h0
    have h1 := congrArg List.length h0
    rw [List.length_map, hord.length_eq, List.length_range] at h1
    cases h1
  have hrun : runE (enc fullc) (ord.map (fun g => mk ((pickD lawN pairN).getD g .top))) = encS (maskOf base J) := by
    rw [hcF, runE_map_encS _ _ hne0, shiftRight_enc, hdec]
  -- the hypotheses of the soundness of the pruned DFS
  have hbad : ∀ i, i < 64 → (badMask 4320 seed).testBit i = false := by
    intro i hi
    rw [testBit_badMask, decide_eq_false (by omega : ¬ 4384 ≤ i), Bool.false_and]
  have hmJ : maskOf base J ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_shiftRight, Nat.zero_mod] at hblk
    exact hne hblk.symm
  have hexact : ∀ i, (badMask 4320 seed).testBit i = true → fullcE.testBit i = true →
      (runE (enc fullc) (ord.map (fun g => mk ((pickD lawN pairN).getD g .top)))).testBit i = false := by
    intro i hb _
    rw [testBit_badMask, Bool.and_eq_true, decide_eq_true_iff] at hb
    obtain ⟨hi, hx⟩ := hb
    rw [hrun, testBit_encS_high _ (by omega)]
    have hk : i - 64 = 4320 + (i - 4384) := by omega
    rw [hk]
    have hsb : seed.testBit (i - 4384) = ((maskOf base J).testBit (4320 + (i - 4384)) && decide (i - 4384 < 720)) := by
      rw [← hblk, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_comm]
    cases h1 : decide (i - 4384 < 720) <;> cases h2 : (maskOf base J).testBit (4320 + (i - 4384))
    · rfl
    · -- outside the block: `i - 4384 ≥ 720` contradicts `decide (i - 4384 < 720) ^^ seed bit = true`
      rw [hsb, h1, h2] at hx
      cases hx
    · rfl
    · rw [hsb, h1, h2] at hx
      cases hx
  have hsound := dfsP_sound (leafF F) fullcE (badMask 4320 seed) hbad _ (enc fullc) hdfs _ hIC
    (by rw [hrun]; exact encS_ne_zero hmJ) hexact
  rw [hrun] at hsound
  unfold leafF at hsound
  rw [shiftRight_encS] at hsound
  intro h0
  rw [h0] at hsound
  cases hsound

end CDCert.K6
