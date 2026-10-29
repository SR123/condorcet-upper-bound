import Condorcet.ExtremeFull

namespace Condorcet
open CondorcetUpperBounds

theorem Connected.mem_right {n : Nat} {D : Domain (Fin n)} {r s : Order (Fin n)}
    (h : Connected D r s) : s ∈ D := by
  obtain ⟨q,hq,heq⟩ := h.mem_end
  exact encode_injective heq ▸ hq

theorem Connected.refl {n : Nat} {D : Domain (Fin n)} {r : Order (Fin n)}
    (hr : r ∈ D) : Connected D r r := Reach.refl ⟨r,hr,rfl⟩

theorem Connected.induction {n : Nat} {D : Domain (Fin n)} {r s : Order (Fin n)}
    (P : Order (Fin n) → Prop) (hstart : P r)
    (hstep : ∀ u ∈ D, ∀ v ∈ D, OneCoordinate (encode u) (encode v) → P u → P v)
    (h : Connected D r s) : P s := by
  have H : ∀ v, Reach (encodedDomain D) (encode r) v →
      ∀ q : Order (Fin n), encode q = v → P q := by
    intro v hv
    induction hv with
    | refl _ =>
      intro q hq
      exact (encode_injective hq).symm ▸ hstart
    | @step b c hab hc hbc ih =>
      obtain ⟨u,hu,heu⟩ := hab.mem_end
      obtain ⟨v,hv,hev⟩ := hc
      intro q hq
      have hs : OneCoordinate (encode u) (encode v) := by simpa [heu,hev] using hbc
      have hp := hstep u hu v hv hs (ih u heu)
      exact encode_injective (hev.trans hq.symm) ▸ hp
  exact H _ h s rfl

/-- Two comparisons forced equal by a never-middle law cannot both change in
one canonical-coordinate step. -/
theorem middle_comparison_step {n : Nat} (r s : Order (Fin n))
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hr : Never r a b c 1) (hs : Never s a b c 1)
    (hstep : OneCoordinate (encode r) (encode s)) : r a b = s a b := by
  have hr' : r a b = r a c := by simpa [Never] using hr
  have hs' : s a b = s a c := by simpa [Never] using hs
  rcases hstep with heq | ⟨k,hk⟩
  · exact congrArg (fun q : Order (Fin n) => q a b) (encode_injective heq)
  · by_cases h1 : (a,b) = k.val
    · have H := comparisons_agree_off_coordinate k hk a c
        (by rw [← h1]; intro h; exact hbc (congrArg Prod.snd h).symm)
        (by rw [← h1]; intro h; exact hac (congrArg Prod.fst h).symm)
      exact hr'.trans (H.trans hs'.symm)
    · by_cases h2 : (b,a) = k.val
      · have H := comparisons_agree_off_coordinate k hk a c
          (by rw [← h2]; intro h; exact hab (congrArg Prod.fst h))
          (by rw [← h2]; intro h; exact hbc (congrArg Prod.fst h).symm)
        exact hr'.trans (H.trans hs'.symm)
      · exact comparisons_agree_off_coordinate k hk a b h1 h2

/-- A common never-middle law fixes both relevant comparisons throughout a component. -/
theorem middle_comparison_fixed {n : Nat} {D : Domain (Fin n)} {r s : Order (Fin n)}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hlaw : ∀ q ∈ D, Never q a b c 1) (h : Connected D r s) : s a b = r a b := by
  apply Connected.induction (fun q => q a b = r a b) rfl _ h
  intro u hu v hv hs hp
  exact (middle_comparison_step u v hab hac hbc (hlaw u hu) (hlaw v hv) hs).symm.trans hp

noncomputable def component {n : Nat} (D : Domain (Fin n)) (r : Order (Fin n)) :
    Domain (Fin n) := by
  classical
  exact D.filter (Connected D r)

def FixedOnComponent {n : Nat} (D : Domain (Fin n)) (r : Order (Fin n)) (i : Pair n) : Prop :=
  ∀ q ∈ D, Connected D r q → encode q i = encode r i

noncomputable def componentPairs {n : Nat} (D : Domain (Fin n))
    (r : Order (Fin n)) : FixedPairs n := by
  classical
  exact fun i => if FixedOnComponent D r i then some (encode r i) else none

theorem connected_holds_componentPairs {n : Nat} {D : Domain (Fin n)}
    {r s : Order (Fin n)} (h : Connected D r s) : HoldsPairs (componentPairs D r) s := by
  classical
  intro i b hb
  unfold componentPairs at hb
  split at hb
  · rename_i hi
    have heq := Option.some.inj hb
    rw [← heq]
    exact hi s h.mem_right h
  · contradiction

theorem holds_componentPairs_fixed {n : Nat} {D : Domain (Fin n)}
    {r s : Order (Fin n)} (h : HoldsPairs (componentPairs D r) s) (i : Pair n)
    (hi : FixedOnComponent D r i) : encode s i = encode r i := by
  classical
  exact h i _ (by simp [componentPairs,hi])

theorem component_membership {n : Nat} {D : Domain (Fin n)} (hD : IsFull D)
    (r s : Order (Fin n)) (hr : r ∈ D) :
    s ∈ component D r ↔ s ∈ D ∧ HoldsPairs (componentPairs D r) s := by
  classical
  simp only [component, Finset.mem_filter]
  constructor
  · rintro ⟨hs,hc⟩
    exact ⟨hs,connected_holds_componentPairs hc⟩
  · rintro ⟨hs,hp⟩
    refine ⟨hs,hD.component_from_fixed r s hr hs ?_⟩
    intro i hi
    exact holds_componentPairs_fixed hp i hi

/-- Agreement with fixed canonical pairs also gives every oriented fixed comparison. -/
theorem holds_componentPairs_comparison {n : Nat} {D : Domain (Fin n)}
    {r s : Order (Fin n)} (h : HoldsPairs (componentPairs D r) s) (a b : Fin n)
    (hfixed : ∀ q ∈ D, Connected D r q → q a b = r a b) : s a b = r a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact holds_componentPairs_fixed h ⟨(a,b),hab⟩ hfixed
  · rw [s.irrefl,r.irrefl]
  · have H : encode s ⟨(b,a),hba⟩ = encode r ⟨(b,a),hba⟩ := by
      apply holds_componentPairs_fixed h
      intro q hq hc
      change q b a = r b a
      rw [q.reverse_comparison (ne_of_lt hba).symm,
        r.reverse_comparison (ne_of_lt hba).symm,hfixed q hq hc]
    change s b a = r b a at H
    rw [s.reverse_comparison (ne_of_lt hba),r.reverse_comparison (ne_of_lt hba),H]

#print axioms middle_comparison_fixed
#print axioms component_membership
#print axioms holds_componentPairs_comparison

theorem replace_middle_on_component {n : Nat} {D : Domain (Fin n)}
    (r : Order (Fin n)) (hr : r ∈ D) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hlaw : ∀ q ∈ D, Never q a b c 1) :
    ∃ p : Fin 3, p ≠ 1 ∧
      (∀ s ∈ component D r, Never s a b c p) ∧
      (∀ s, HoldsPairs (componentPairs D r) s → Never s a b c 1) := by
  classical
  have hfix : ∀ q ∈ D, Connected D r q → q a b = r a b :=
    fun q _ hc => middle_comparison_fixed hab hac hbc hlaw hc
  have hfix' : ∀ q ∈ D, Connected D r q → q a c = r a c := by
    intro q hq hc
    exact middle_comparison_fixed hac hab hbc.symm
      (fun s hs => (Never.swap s a b c 1).mp (hlaw s hs)) hc
  have hrestore : ∀ s, HoldsPairs (componentPairs D r) s → Never s a b c 1 := by
    intro s hs
    have h₁ := holds_componentPairs_comparison hs a b hfix
    have h₂ := holds_componentPairs_comparison hs a c hfix'
    simpa [Never,h₁,h₂] using hlaw r hr
  by_cases hb : r a b = true
  · refine ⟨2,by decide,?_,hrestore⟩
    intro s hs
    have hc := (Finset.mem_filter.mp hs).2
    have H : s a b = true := (hfix s (Finset.mem_filter.mp hs).1 hc).trans hb
    simp [Never,H]
  · have hb' : r a b = false := Bool.eq_false_iff.mpr hb
    refine ⟨0,by decide,?_,hrestore⟩
    intro s hs
    have hc := (Finset.mem_filter.mp hs).2
    have H : s a b = false := (hfix s (Finset.mem_filter.mp hs).1 hc).trans hb'
    simp [Never,H]

/-- Replace one selected law on a component. Middle laws become extreme laws
implied by a fixed comparison; the original law follows from the fixed pairs. -/
theorem component_choose_extreme_law {n : Nat} (L : Selection n)
    (r : Order (Fin n)) (hr : r ∈ fullDomain L) (t : Triple n) :
    ∃ law : Fin 3 × Fin 3, law.2 ≠ 1 ∧
      (∀ s ∈ component (fullDomain L) r, HoldsLaw s t law) ∧
      (∀ s, HoldsPairs (componentPairs (fullDomain L) r) s →
        HoldsLaw s t law → HoldsLaw s t (L t)) := by
  classical
  have hL : ∀ s ∈ fullDomain L, HoldsLaw s t (L t) :=
    fun s hs => (mem_fullDomain L s).mp hs t
  rcases hEq : L t with ⟨x,p⟩
  by_cases hp : p = 1
  · subst p
    have hab := ne_of_lt t.property.1
    have hac := ne_of_lt (lt_trans t.property.1 t.property.2)
    have hbc := ne_of_lt t.property.2
    fin_cases x
    · have hmid : ∀ s ∈ fullDomain L, Never s t.val.1 t.val.2.1 t.val.2.2 1 := by
        intro s hs
        simpa [hEq,HoldsLaw] using hL s hs
      obtain ⟨p,hp,hcomp,hrestore⟩ := replace_middle_on_component r hr _ _ _ hab hac hbc hmid
      refine ⟨(0,p),hp,?_,?_⟩
      · exact hcomp
      · intro s hs _
        simpa [hEq,HoldsLaw] using hrestore s hs
    · have hmid : ∀ s ∈ fullDomain L, Never s t.val.2.1 t.val.1 t.val.2.2 1 := by
        intro s hs
        simpa [hEq,HoldsLaw] using hL s hs
      obtain ⟨p,hp,hcomp,hrestore⟩ := replace_middle_on_component r hr _ _ _ hab.symm hbc hac hmid
      refine ⟨(1,p),hp,?_,?_⟩
      · exact hcomp
      · intro s hs _
        simpa [hEq,HoldsLaw] using hrestore s hs
    · have hmid : ∀ s ∈ fullDomain L, Never s t.val.2.2 t.val.1 t.val.2.1 1 := by
        intro s hs
        simpa [hEq,HoldsLaw] using hL s hs
      obtain ⟨p,hp,hcomp,hrestore⟩ := replace_middle_on_component r hr _ _ _ hac.symm hbc.symm hab hmid
      refine ⟨(2,p),hp,?_,?_⟩
      · exact hcomp
      · intro s hs _
        simpa [hEq,HoldsLaw] using hrestore s hs
  · refine ⟨(x,p),hp,?_,?_⟩
    · intro s hs
      have H := hL s (Finset.mem_filter.mp hs).1
      simpa [hEq] using H
    · intro s _ hs
      simpa [hEq] using hs

/-- Every adjacent-swap component of a full CD is exactly a full solution set
of extreme never-laws and fixed pair comparisons. -/
theorem IsFull.component_isExtremeFull {n : Nat} {D : Domain (Fin n)}
    (hD : IsFull D) (r : Order (Fin n)) (hr : r ∈ D) : IsExtremeFull (component D r) := by
  classical
  obtain ⟨L,rfl⟩ := hD
  choose N hN hcomp hrestore using component_choose_extreme_law L r hr
  let N' : ExtremeSelection n := ⟨N,hN⟩
  refine ⟨N',componentPairs (fullDomain L) r,?_⟩
  ext s
  rw [mem_extremeFullDomain]
  constructor
  · intro hs
    exact ⟨fun t => hcomp t s hs,
      ((component_membership ⟨L,rfl⟩ r s hr).mp hs).2⟩
  · rintro ⟨hs,hpairs⟩
    apply (component_membership ⟨L,rfl⟩ r s hr).mpr
    refine ⟨(mem_fullDomain L s).mpr ?_,hpairs⟩
    intro t
    exact hrestore t s hpairs (hs t)

theorem IsFull.component_inF {n : Nat} {D : Domain (Fin n)}
    (hD : IsFull D) (r : Order (Fin n)) (hr : r ∈ D) : InF (component D r) := by
  classical
  refine ⟨⟨r,Finset.mem_filter.mpr ⟨hr,Connected.refl hr⟩⟩,
    hD.component_isExtremeFull r hr⟩

#print axioms IsFull.component_isExtremeFull
#print axioms IsFull.component_inF

end Condorcet
