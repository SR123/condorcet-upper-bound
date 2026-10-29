import Condorcet.Insertion

namespace Condorcet
variable {α : Type*} [Fintype α]

/-- The actual occupied insertion slots above a fixed deleted order. -/
noncomputable def insertionSlots (D : Domain (Option α)) (P : Order α) :
    Finset (Fin (Fintype.card α + 1)) := by
  classical
  exact Finset.univ.filter (fun t => P.insertAt t ∈ D)

noncomputable def orderFibre (D : Domain (Option α)) (P : Order α) : Domain (Option α) :=
  D.filter (fun s => Order.restrict Order.someEmbedding s = P)

@[simp] theorem mem_insertionSlots (D : Domain (Option α)) (P : Order α)
    (t : Fin (Fintype.card α + 1)) : t ∈ insertionSlots D P ↔ P.insertAt t ∈ D := by
  classical
  simp [insertionSlots]

/-- Slot enumeration is exactly the actual order fibre, with nothing missed. -/
theorem image_insertionSlots (D : Domain (Option α)) (P : Order α) :
    (insertionSlots D P).image P.insertAt = orderFibre D P := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨(mem_insertionSlots D P t).mp ht, Order.restrict_insertAt P t⟩
  · intro hs
    obtain ⟨hs,hP⟩ := Finset.mem_filter.mp hs
    have hrec : P.insertAt s.insertionSlot = s := by
      simpa only [hP] using s.reconstruct_insertion
    exact Finset.mem_image.mpr ⟨s.insertionSlot,
      (mem_insertionSlots D P _).mpr (hrec.symm ▸ hs),hrec⟩

theorem card_insertionSlots (D : Domain (Option α)) (P : Order α) :
    (insertionSlots D P).card = (orderFibre D P).card := by
  classical
  rw [← image_insertionSlots, Finset.card_image_of_injective _ P.insertAt_injective]

theorem insertionSlots_nonempty (D : Domain (Option α)) (P : Order α) :
    (insertionSlots D P).Nonempty ↔ P ∈ restrictDomain Order.someEmbedding D := by
  constructor
  · rintro ⟨t,ht⟩
    exact (mem_restrictDomain _ D P).mpr ⟨P.insertAt t,(mem_insertionSlots D P t).mp ht,
      Order.restrict_insertAt P t⟩
  · intro hP
    obtain ⟨s,hs,hPs⟩ := (mem_restrictDomain _ D P).mp hP
    have hrec : P.insertAt s.insertionSlot = s := by
      simpa only [hPs] using s.reconstruct_insertion
    exact ⟨s.insertionSlot,(mem_insertionSlots D P _).mpr (hrec.symm ▸ hs)⟩

/-- Every order is counted once among the actual insertion fibres. -/
theorem sum_card_insertionSlots (D : Domain (Option α)) :
    ∑ P ∈ restrictDomain Order.someEmbedding D, (insertionSlots D P).card = D.card := by
  classical
  simp only [card_insertionSlots, orderFibre, restrictDomain]
  exact (Finset.card_eq_sum_card_image (Order.restrict Order.someEmbedding) D).symm

#print axioms image_insertionSlots
#print axioms insertionSlots_nonempty
#print axioms sum_card_insertionSlots
end Condorcet
