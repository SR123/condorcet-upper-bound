/-
CDCert.Levels — level-closure certificates.

Depth-first checking explores every path of the search tree; on six
alternatives that can be tens of millions of leaves even when only a few
hundred distinct domains arise (measured: 59.5 M leaves versus at most 2,072
distinct states per level for one peak-pit slice). Merging equal states inside
the kernel requires long-list processing, which overflows or exhausts memory.

Instead, the external generator supplies, for every level, the set of states
it reached (deduplicated, as a binary search tree), and Lean checks only:
* closure: every state of level i is pruned, or each of its successors is in
  the set of level i+1;
* leaves: every state of the last level passes `leafOK`;
* the start state is in the set of level 0.

Soundness (`certOK_sound`, `coverage_of_certB`) needs no property of the
certificate or of the tree's ordering: a wrong or incomplete certificate
simply makes the check fail. Every comparison descends one tree level, so
kernel recursion depth stays logarithmic.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Bitset

namespace CDCert

/-! ### Abstract invariant principle -/

section Invariant
variable {σ ω : Type}

/-- **Invariant principle.** If `inv` (indexed by the remaining groups) is
closed under every non-pruned transition, and every invariant leaf meeting the
goal passes `leafOK`, then every choice whose result meets the goal passes. -/
theorem invariant_sound {act : ω → σ → σ} {prune : List (List ω) → σ → Bool}
    {goal leafOK : σ → Bool} (hp : PruneSoundFor act prune goal)
    (inv : List (List ω) → σ → Prop)
    (hstep : ∀ g gs s, inv (g :: gs) s → prune (g :: gs) s = false →
      ∀ o, o ∈ g → inv gs (act o s))
    (hleaf : ∀ s, inv [] s → goal s = true → leafOK s = true) :
    ∀ (gs : List (List ω)) (s : σ), inv gs s →
      ∀ c, IsChoice c gs → goal (runChoice act s c) = true →
        leafOK (runChoice act s c) = true := by
  intro gs
  induction gs with
  | nil =>
    intro s hs c hc hg
    rw [isChoice_nil_iff] at hc
    subst hc
    exact hleaf s hs hg
  | cons g gs ih =>
    intro s hs c hc hg
    cases hpr : prune (g :: gs) s with
    | true =>
      rw [hp (g :: gs) s hpr c hc] at hg
      cases hg
    | false =>
      obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
      exact ih (act o s) (hstep g gs s hs hpr o ho) c' hc' hg

end Invariant

namespace Bits

/-! ### Binary search trees of naturals (soundness needs no ordering invariant) -/

/-- A binary tree of naturals, used as a set with logarithmic lookup. -/
inductive NTree where
  | leaf : NTree
  | node : NTree → Nat → NTree → NTree
deriving Repr

namespace NTree

/-- Semantic membership. -/
def Mem (x : Nat) : NTree → Prop
  | leaf => False
  | node l k r => x = k ∨ Mem x l ∨ Mem x r

/-- Lookup by descending with comparisons. -/
def mem (x : Nat) : NTree → Bool
  | leaf => false
  | node l k r => if x = k then true else if x < k then mem x l else mem x r

/-- Every key satisfies `p`. -/
def all (p : Nat → Bool) : NTree → Bool
  | leaf => true
  | node l k r => p k && all p l && all p r

theorem mem_sound (x : Nat) : ∀ (t : NTree), t.mem x = true → t.Mem x := by
  intro t
  induction t with
  | leaf => intro h; cases h
  | node l k r ihl ihr =>
    intro h
    simp only [mem] at h
    by_cases hk : x = k
    · exact Or.inl hk
    · rw [if_neg hk] at h
      by_cases hlt : x < k
      · rw [if_pos hlt] at h
        exact Or.inr (Or.inl (ihl h))
      · rw [if_neg hlt] at h
        exact Or.inr (Or.inr (ihr h))

theorem all_sound (p : Nat → Bool) : ∀ (t : NTree), t.all p = true → ∀ x, t.Mem x → p x = true := by
  intro t
  induction t with
  | leaf => intro _ x hx; cases hx
  | node l k r ihl ihr =>
    intro h x hx
    simp only [all, Bool.and_eq_true] at h
    obtain ⟨⟨hk, hl⟩, hr⟩ := h
    rcases hx with rfl | hx | hx
    · exact hk
    · exact ihl hl x hx
    · exact ihr hr x hx

end NTree

/-! ### A cached-friendly prune and its soundness -/

/-- Prune with a precomputable intersection: `retainAll gs top` depends only on
the remaining groups, so the kernel can share it across all states of a level.
Sound for every `top`. -/
def pruneC (fM top : Nat) (gs : List (List Nat)) (m : Nat) : Bool :=
  ((m &&& fM) &&& retainAll gs top) != 0

theorem pruneC_sound (eM sM top : Nat) :
    PruneSoundFor andAct (pruneC (forbiddenMask eM sM) top) (exactB eM sM) := by
  intro gs m hp c hc
  have hne : ((m &&& forbiddenMask eM sM) &&& retainAll gs top) ≠ 0 := by
    simpa [pruneC] using hp
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  rw [Nat.testBit_and, Nat.testBit_and, testBit_retainAll, testBit_forbiddenMask] at hi
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hi
  obtain ⟨⟨hm, heM, hsM⟩, _, hall⟩ := hi
  have hr : (runChoice andAct m c).testBit i = true := by
    rw [testBit_runChoice_andAct, hm, Bool.true_and, List.all_eq_true]
    intro k hk
    obtain ⟨g, hg, hkg⟩ := hc.exists_group k hk
    exact hall g hg k hkg
  cases h : exactB eM sM (runChoice andAct m c) with
  | false => rfl
  | true =>
    have heq : (runChoice andAct m c &&& eM) = sM := by simpa [exactB] using h
    have := congrArg (fun x => x.testBit i) heq
    simp only [Nat.testBit_and, hr, heM, hsM, Bool.true_and] at this
    cases this

/-! ### Level-closure certificates over bitset states -/

/-- One level: every state of `L` is pruned or has all successors in `L'`. -/
def stepOK (prune : List (List Nat) → Nat → Bool) (g : List Nat) (gs : List (List Nat))
    (L L' : NTree) : Bool :=
  L.all (fun s => prune (g :: gs) s || g.all (fun o => L'.mem (s &&& o)))

/-- A certificate: one tree per level, aligned with the suffixes of the groups. -/
def certOK (prune : List (List Nat) → Nat → Bool) (leafOK : Nat → Bool) :
    List (List Nat) → List NTree → Bool
  | [], [L] => L.all leafOK
  | g :: gs, L :: L' :: Ls => stepOK prune g gs L L' && certOK prune leafOK gs (L' :: Ls)
  | _, _ => false

theorem certOK_sound {prune : List (List Nat) → Nat → Bool} {goal leafOK : Nat → Bool}
    (hp : PruneSoundFor andAct prune goal) :
    ∀ (gs : List (List Nat)) (L : NTree) (Ls : List NTree) (s : Nat),
      certOK prune leafOK gs (L :: Ls) = true → L.Mem s →
      ∀ c, IsChoice c gs → goal (runChoice andAct s c) = true →
        leafOK (runChoice andAct s c) = true := by
  intro gs
  induction gs with
  | nil =>
    intro L Ls s h hs c hc _
    rw [isChoice_nil_iff] at hc
    subst hc
    cases Ls with
    | nil => exact NTree.all_sound leafOK L h s hs
    | cons _ _ => cases h
  | cons g gs ih =>
    intro L Ls s h hs c hc hg
    cases Ls with
    | nil => cases h
    | cons L' Ls =>
      simp only [certOK, Bool.and_eq_true] at h
      obtain ⟨hstep, hrest⟩ := h
      have hsOK := NTree.all_sound _ L hstep s hs
      simp only [Bool.or_eq_true, List.all_eq_true] at hsOK
      rcases hsOK with hpr | hall
      · rw [hp (g :: gs) s hpr c hc] at hg
        cases hg
      · obtain ⟨o, ho, c', hc', rfl⟩ := isChoice_cons_iff.mp hc
        exact ih L' Ls (s &&& o) hrest (NTree.mem_sound _ L' (hall o ho)) c' hc' hg

/-- **Transfer theorem for certificates.** A successful certificate check over
the required-slice-filtered bitset groups proves `P` for every domain defined
by a choice for `gs` whose `E`-slice is exactly `S`. -/
theorem coverage_of_certB {α : Type} [DecidableEq α] {base : List α} (hnd : base.Nodup)
    (gs : List (Group α)) (E : α → Bool) (S : List α)
    (hSb : ∀ s, s ∈ S → s ∈ base) (hSE : ∀ s, s ∈ S → E s = true)
    (top : Nat) (leafOK : Nat → Bool) (P : List α → Prop)
    (hleaf : ∀ m, exactB (maskOf base E) (maskOf base (optOfList S)) m = true →
      leafOK m = true → P (decode base m))
    (L : NTree) (Ls : List NTree)
    (hstart : L.Mem (maskOf base (fun _ => true)))
    (h : certOK (pruneC (forbiddenMask (maskOf base E) (maskOf base (optOfList S))) top)
          leafOK (requireSliceB (maskOf base (optOfList S)) (gs.map (List.map (maskOf base))))
          (L :: Ls) = true) :
    ∀ c, IsChoice c gs → ExactSlice E S (domainOf base c) → P (domainOf base c) := by
  intro c hc hx
  have hcB := hc.map (maskOf base)
  have hdec := decode_runChoice_full base c
  have hxB : exactB (maskOf base E) (maskOf base (optOfList S))
      (runChoice andAct (maskOf base (fun _ => true)) (c.map (maskOf base))) = true := by
    rw [exactB_iff hnd hSb hSE, hdec]
    exact hx
  have hcF : IsChoice (c.map (maskOf base))
      (requireSliceB (maskOf base (optOfList S)) (gs.map (List.map (maskOf base)))) :=
    IsChoice.filter _ hcB (subB_of_exactB hxB)
  have hl := certOK_sound (pruneC_sound _ _ top) _ L Ls _ h hstart _ hcF hxB
  rw [← hdec]
  exact hleaf _ hxB hl

end Bits

end CDCert
