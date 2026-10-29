import Condorcet.MedianClosure

namespace Condorcet
open CondorcetUpperBounds

/-- Two orders differ by exchanging a consecutive pair; every other comparison
is unchanged. This definition refers directly to strict total orders. -/
def AdjacentSwap {n : Nat} (r s : Order (Fin n)) : Prop :=
  ∃ a b, a ≠ b ∧ r a b = true ∧ s a b = false ∧
    (∀ c, ¬(r a c = true ∧ r c b = true)) ∧
    (∀ x y, (x,y) ≠ (a,b) → (x,y) ≠ (b,a) → r x y = s x y)

theorem comparisons_agree_off_coordinate {n : Nat} {r s : Order (Fin n)}
    (k : Pair n) (h : ∀ i, i ≠ k → encode r i = encode s i)
    (a b : Fin n) (h₁ : (a,b) ≠ k.val) (h₂ : (b,a) ≠ k.val) : r a b = s a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact h ⟨(a,b),hab⟩ (fun heq => h₁ (congrArg Subtype.val heq))
  · rw [r.irrefl, s.irrefl]
  · have H := h ⟨(b,a),hba⟩ (fun heq => h₂ (congrArg Subtype.val heq))
    change r b a = s b a at H
    rw [r.reverse_comparison (ne_of_lt hba), s.reverse_comparison (ne_of_lt hba), H]

theorem consecutive_of_only_pair_changed {n : Nat} {r s : Order (Fin n)}
    {a b : Fin n} (hs : s a b = false)
    (h : ∀ x y, (x,y) ≠ (a,b) → (x,y) ≠ (b,a) → r x y = s x y) :
    ∀ c, ¬(r a c = true ∧ r c b = true) := by
  intro c ⟨hac,hcb⟩
  have hca : c ≠ a := by intro heq; subst c; rw [r.irrefl] at hac; contradiction
  have hcb' : c ≠ b := by intro heq; subst c; rw [r.irrefl] at hcb; contradiction
  have ha : r a c = s a c := h a c
    (fun heq => hcb' (congrArg Prod.snd heq))
    (fun heq => hca (congrArg Prod.snd heq))
  have hb : r c b = s c b := h c b
    (fun heq => hca (congrArg Prod.fst heq))
    (fun heq => hcb' (congrArg Prod.fst heq))
  have H := s.trans (ha ▸ hac) (hb ▸ hcb)
  rw [hs] at H
  contradiction

theorem oneCoordinate_iff_adjacent {n : Nat} (r s : Order (Fin n)) :
    OneCoordinate (encode r) (encode s) ↔ r = s ∨ AdjacentSwap r s := by
  constructor
  · intro H
    rcases H with H | ⟨k,hk⟩
    · exact Or.inl (encode_injective H)
    · by_cases heq : encode r k = encode s k
      · left
        apply encode_injective
        funext i
        by_cases hi : i = k
        · simpa [hi] using heq
        · exact hk i hi
      · have hne : k.val.1 ≠ k.val.2 := ne_of_lt k.property
        have hoff : ∀ x y, (x,y) ≠ k.val → (x,y) ≠ (k.val.2,k.val.1) → r x y = s x y := by
          intro x y h₁ h₂
          apply comparisons_agree_off_coordinate k hk x y h₁
          intro heq'
          apply h₂
          have ha := congrArg Prod.fst heq'
          have hb := congrArg Prod.snd heq'
          exact Prod.ext hb ha
        change r k.val.1 k.val.2 ≠ s k.val.1 k.val.2 at heq
        cases hr : r k.val.1 k.val.2 <;> cases hs : s k.val.1 k.val.2
        · exact False.elim (heq (hr.trans hs.symm))
        · right
          have hr' : r k.val.2 k.val.1 = true := by rw [r.reverse_comparison hne, hr]; rfl
          have hs' : s k.val.2 k.val.1 = false := by rw [s.reverse_comparison hne, hs]; rfl
          have hoff' : ∀ x y, (x,y) ≠ (k.val.2,k.val.1) → (x,y) ≠ (k.val.1,k.val.2) → r x y = s x y :=
            fun x y h₁ h₂ => hoff x y h₂ h₁
          exact ⟨k.val.2, k.val.1, hne.symm, hr', hs',
            consecutive_of_only_pair_changed hs' hoff', hoff'⟩
        · exact Or.inr ⟨k.val.1, k.val.2, hne, hr, hs,
            consecutive_of_only_pair_changed hs hoff, hoff⟩
        · exact False.elim (heq (hr.trans hs.symm))
  · intro H
    rcases H with rfl | ⟨a,b,hab,_,_,_,hoff⟩
    · exact Or.inl rfl
    · right
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · refine ⟨⟨(a,b),hlt⟩, ?_⟩
        intro i hi
        apply hoff i.val.1 i.val.2
        · intro heq
          exact hi (Subtype.ext heq)
        · intro heq
          have H := i.property
          rw [show i.val.1 = b from congrArg Prod.fst heq,
              show i.val.2 = a from congrArg Prod.snd heq] at H
          exact (lt_asymm hlt H)
      · refine ⟨⟨(b,a),hgt⟩, ?_⟩
        intro i hi
        apply hoff i.val.1 i.val.2
        · intro heq
          have H := i.property
          rw [show i.val.1 = a from congrArg Prod.fst heq,
              show i.val.2 = b from congrArg Prod.snd heq] at H
          exact (lt_asymm hgt H)
        · intro heq
          exact hi (Subtype.ext heq)

/-- Connectivity through actual orders. The equivalence above establishes that
its nonstationary elementary steps are precisely adjacent swaps. -/
def Connected {n : Nat} (D : Domain (Fin n)) (r s : Order (Fin n)) : Prop :=
  Reach (encodedDomain D) (encode r) (encode s)

/-- Actual maximal-domain components are determined by their fixed comparisons. -/
theorem IsMaximal.component_from_fixed {n : Nat} {D : Domain (Fin n)}
    (hD : IsMaximal D) (r s : Order (Fin n)) (hr : r ∈ D) (hs : s ∈ D)
    (hfixed : ∀ i : Pair n,
      (∀ q ∈ D, Connected D r q → encode q i = encode r i) → encode s i = encode r i) :
    Connected D r s := by
  classical
  apply component_from_fixed_coordinates (encodedDomain D) hD.encoded_medianClosed
    (encode r) (encode s) ⟨r,hr,rfl⟩ ⟨s,hs,rfl⟩ (Finset.univ.toList) (by simp)
  intro i H
  exact hfixed i (fun q _ hq => H (encode q) hq)

#print axioms oneCoordinate_iff_adjacent
#print axioms IsMaximal.component_from_fixed
end Condorcet
