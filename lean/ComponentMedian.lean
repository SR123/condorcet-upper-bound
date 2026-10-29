import MajorityLaws

/-!
Connected components of a majority-closed Boolean comparison family are
exactly its members that agree with the coordinates fixed on the component.
This is the abstract median/projection part of paper Lemma2.2. Connecting
these Boolean families to actual transitive orders is carried out in
Condorcet.Adjacency, FullDomains and Components.
-/
namespace CondorcetUpperBounds

variable {I : Type}

def MedianClosed (D : (I → Bool) → Prop) : Prop :=
  ∀ u v w, D u → D v → D w → D (comparisonMajority u v w)

inductive Reach (D : (I → Bool) → Prop) : (I → Bool) → (I → Bool) → Prop
  | refl {p} : D p → Reach D p p
  | step {p q r} : Reach D p q → D r → OneCoordinate q r → Reach D p r

theorem Reach.mem_end {D : (I → Bool) → Prop} {p q : I → Bool}
    (h : Reach D p q) : D q := by
  cases h with
  | refl hp => exact hp
  | step _ hq _ => exact hq

theorem Reach.trans {D : (I → Bool) → Prop} {p q r : I → Bool}
    (hpq : Reach D p q) (hqr : Reach D q r) : Reach D p r := by
  induction hqr with
  | refl _ => exact hpq
  | step _ hr hs ih => exact Reach.step ih hr hs

theorem OneCoordinate.symm {u v : I → Bool} (h : OneCoordinate u v) :
    OneCoordinate v u := by
  cases h with
  | inl h => exact Or.inl h.symm
  | inr h =>
    obtain ⟨k, hk⟩ := h
    exact Or.inr ⟨k, fun i hi => (hk i hi).symm⟩

theorem Reach.reverse {D : (I → Bool) → Prop} {p q : I → Bool}
    (h : Reach D p q) : Reach D q p := by
  induction h with
  | refl hp => exact Reach.refl hp
  | step hpq hr hs ih =>
    have hrq := Reach.step (Reach.refl hr) hpq.mem_end hs.symm
    exact hrq.trans ih

theorem Reach.map {D : (I → Bool) → Prop} {p q : I → Bool}
    (h : Reach D p q) (f : (I → Bool) → (I → Bool))
    (hmem : ∀ u, D u → D (f u))
    (hstep : ∀ u v, OneCoordinate u v → OneCoordinate (f u) (f v)) :
    Reach D (f p) (f q) := by
  induction h with
  | refl hp => exact Reach.refl (hmem _ hp)
  | step _ hr hs ih => exact Reach.step ih (hmem _ hr) (hstep _ _ hs)

theorem median_last_two : ∀ a b : Bool, median a b b = b := by decide

theorem component_coordinate_approximation
    (D : (I → Bool) → Prop) (closed : MedianClosed D)
    (root target : I → Bool) (hroot : D root) (htarget : D target)
    (attainable : ∀ i, ∃ v, Reach D root v ∧ v i = target i)
    (coordinates : List I) :
    ∃ v, Reach D root v ∧ ∀ i, i ∈ coordinates → v i = target i := by
  induction coordinates with
  | nil => exact ⟨root, Reach.refl hroot, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons i rest ih =>
    obtain ⟨v, hv, hagree⟩ := ih
    obtain ⟨w, hw, hwi⟩ := attainable i
    let f := comparisonMajority v target
    have mapped : Reach D (f v) (f w) :=
      (hv.reverse.trans hw).map f
        (fun u hu => closed v target u hv.mem_end htarget hu)
        (fun u w h => projection_preserves_step v target u w h)
    have hstart : f v = v := by
      funext j
      exact median_self (v j) (target j)
    rw [hstart] at mapped
    refine ⟨f w, hv.trans mapped, ?_⟩
    intro j hj
    have casesJ : j = i ∨ j ∈ rest := by simpa only [List.mem_cons] using hj
    cases casesJ with
    | inl heq =>
      subst j
      change median (v i) (target i) (w i) = target i
      rw [hwi]
      exact median_last_two (v i) (target i)
    | inr hrest =>
      change comparisonMajority v target w j = target j
      rw [projection_fixes_agreement v target w j (hagree j hrest)]
      exact hagree j hrest

/-- The finite-coordinate component theorem with coordinate attainability. -/
theorem component_from_attainable_coordinates
    (D : (I → Bool) → Prop) (closed : MedianClosed D)
    (root target : I → Bool) (hroot : D root) (htarget : D target)
    (coordinates : List I) (covers : ∀ i, i ∈ coordinates)
    (attainable : ∀ i, ∃ v, Reach D root v ∧ v i = target i) :
    Reach D root target := by
  obtain ⟨v, hv, hagree⟩ := component_coordinate_approximation
    D closed root target hroot htarget attainable coordinates
  have hveq : v = target := by
    funext i
    exact hagree i (covers i)
  rw [hveq] at hv
  exact hv

theorem bool_two_values : ∀ a b c : Bool, a ≠ b → c ≠ b → c = a := by decide

/-- Actual fixed-coordinate form used in the paper. -/
theorem component_from_fixed_coordinates
    (D : (I → Bool) → Prop) (closed : MedianClosed D)
    (root target : I → Bool) (hroot : D root) (htarget : D target)
    (coordinates : List I) (covers : ∀ i, i ∈ coordinates)
    (agrees_fixed : ∀ i, (∀ v, Reach D root v → v i = root i) →
                         target i = root i) : Reach D root target := by
  classical
  apply component_from_attainable_coordinates D closed root target hroot htarget coordinates covers
  intro i
  by_cases h : ∃ v, Reach D root v ∧ v i = target i
  · exact h
  · have hdiff : root i ≠ target i := by
      intro heq
      exact h ⟨root, Reach.refl hroot, heq⟩
    have hfixed : ∀ v, Reach D root v → v i = root i := by
      intro v hv
      have hvdiff : v i ≠ target i := by
        intro heq
        exact h ⟨v, hv, heq⟩
      exact bool_two_values (root i) (target i) (v i) hdiff hvdiff
    have htargeteq := agrees_fixed i hfixed
    exact False.elim (hdiff htargeteq.symm)

#print axioms component_coordinate_approximation
#print axioms component_from_attainable_coordinates
#print axioms component_from_fixed_coordinates
end CondorcetUpperBounds
