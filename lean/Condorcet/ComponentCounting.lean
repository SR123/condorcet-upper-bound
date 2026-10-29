import Condorcet.Components
import Condorcet.NoGaps

namespace Condorcet
open CondorcetUpperBounds

theorem Connected.symm {n : Nat} {D : Domain (Fin n)} {r s : Order (Fin n)}
    (h : Connected D r s) : Connected D s r := Reach.reverse h

theorem Connected.trans {n : Nat} {D : Domain (Fin n)} {r s t : Order (Fin n)}
    (h : Connected D r s) (h' : Connected D s t) : Connected D r t := Reach.trans h h'

@[simp] theorem mem_component {n : Nat} (D : Domain (Fin n)) (r s : Order (Fin n)) :
    s ∈ component D r ↔ s ∈ D ∧ Connected D r s := by
  classical
  exact Finset.mem_filter

theorem component_eq_of_connected {n : Nat} {D : Domain (Fin n)} {r s : Order (Fin n)}
    (h : Connected D r s) : component D r = component D s := by
  ext t
  simp only [mem_component]
  exact ⟨fun ⟨ht,hc⟩ => ⟨ht,h.symm.trans hc⟩, fun ⟨ht,hc⟩ => ⟨ht,h.trans hc⟩⟩

noncomputable def components {n : Nat} (D : Domain (Fin n)) : Finset (Domain (Fin n)) := by
  classical
  exact D.image (component D)

theorem mem_components {n : Nat} (D : Domain (Fin n)) (K : Domain (Fin n)) :
    K ∈ components D ↔ ∃ r ∈ D, component D r = K := by
  classical
  exact Finset.mem_image

theorem component_mem_components {n : Nat} {D : Domain (Fin n)} {r : Order (Fin n)}
    (hr : r ∈ D) : component D r ∈ components D :=
  (mem_components _ _).mpr ⟨r,hr,rfl⟩

theorem mem_component_iff_component_eq {n : Nat} {D K : Domain (Fin n)}
    (hK : K ∈ components D) {s : Order (Fin n)} :
    s ∈ K ↔ s ∈ D ∧ component D s = K := by
  obtain ⟨r,hr,rfl⟩ := (mem_components _ _).mp hK
  constructor
  · intro hs
    obtain ⟨hs,hc⟩ := (mem_component _ _ _).mp hs
    exact ⟨hs,(component_eq_of_connected hc).symm⟩
  · rintro ⟨hs,heq⟩
    rw [← heq]
    exact (mem_component _ _ _).mpr ⟨hs,Connected.refl hs⟩

theorem components_biUnion {n : Nat} (D : Domain (Fin n)) :
    (components D).biUnion id = D := by
  classical
  ext s
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨K,hK,hs⟩
    exact ((mem_component_iff_component_eq hK).mp hs).1
  · intro hs
    exact ⟨component D s,component_mem_components hs,
      (mem_component _ _ _).mpr ⟨hs,Connected.refl hs⟩⟩

theorem components_pairwise_disjoint {n : Nat} (D : Domain (Fin n)) :
    (components D : Set (Domain (Fin n))).PairwiseDisjoint id := by
  classical
  intro K hK L hL hne
  apply Finset.disjoint_left.mpr
  intro s hs ht
  have h₁ := ((mem_component_iff_component_eq hK).mp hs).2
  have h₂ := ((mem_component_iff_component_eq hL).mp ht).2
  exact hne (h₁.symm.trans h₂)

theorem sum_components_card {n : Nat} (D : Domain (Fin n)) :
    ∑ K ∈ components D, K.card = D.card := by
  classical
  calc
    _ = ((components D).biUnion id).card :=
      (Finset.card_biUnion (components_pairwise_disjoint D)).symm
    _ = D.card := congrArg Finset.card (components_biUnion D)

theorem IsFull.components_inF {n : Nat} {D K : Domain (Fin n)}
    (hD : IsFull D) (hK : K ∈ components D) : InF K := by
  obtain ⟨r,hr,rfl⟩ := (mem_components _ _).mp hK
  exact hD.component_inF r hr

namespace SlotWord

theorem edges_cons_eq (prev b : Bool) (bs : List Bool) :
    edges prev (b :: bs) = (if prev && b then 1 else 0) + adjacentPairs (b :: bs) := by
  simp [edges,adjacentPairs]

theorem adjacentPairs_ofFn {m : Nat} (f : Fin (m+1) → Bool) :
    adjacentPairs (List.ofFn f) =
      ∑ i : Fin m, if f i.castSucc && f i.succ then 1 else 0 := by
  induction m with
  | zero => simp [List.ofFn_succ,adjacentPairs,edges]
  | succ m ih =>
    rw [List.ofFn_succ]
    simp only [adjacentPairs, edges, Bool.false_and, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [List.ofFn_succ, edges_cons_eq]
    have H := ih (fun i => f i.succ)
    rw [List.ofFn_succ] at H
    rw [H, Fin.sum_univ_succ]
    rfl

end SlotWord

#print axioms sum_components_card
#print axioms IsFull.components_inF
#print axioms SlotWord.adjacentPairs_ofFn
end Condorcet
