import Condorcet.ValueRestriction

namespace Condorcet
open CondorcetUpperBounds

abbrev Pattern := Bool × Bool × Bool

def Pattern.Valid (t : Pattern) : Prop :=
  (t.1 = true → t.2.2 = true → t.2.1 = true) ∧
  (t.1 = false → t.2.2 = false → t.2.1 = false)

def Pattern.code (t : Pattern) : Fin 6 :=
  if t.1 then if t.2.1 then if t.2.2 then 0 else 1 else 4
  else if t.2.1 then 2 else if t.2.2 then 3 else 5

def Pattern.ofCode (k : Fin 6) : Pattern :=
  match k.val with
  | 0 => (true, true, true)
  | 1 => (true, true, false)
  | 2 => (false, true, true)
  | 3 => (false, false, true)
  | 4 => (true, false, false)
  | _ => (false, false, false)

def Pattern.med (s t u : Pattern) : Pattern :=
  (median s.1 t.1 u.1, median s.2.1 t.2.1 u.2.1, median s.2.2 t.2.2 u.2.2)

def NeverBits (a b : Bool) (p : Fin 3) : Prop :=
  if p = 0 then a = false ∨ b = false
  else if p = 1 then a = b
  else a = true ∨ b = true

def Pattern.Never (t : Pattern) (x p : Fin 3) : Prop :=
  if x = 0 then NeverBits t.1 t.2.1 p
  else if x = 1 then NeverBits (!t.1) t.2.2 p
  else NeverBits (!t.2.1) (!t.2.2) p

instance (t : Pattern) : Decidable t.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (t : Pattern) (x p : Fin 3) : Decidable (t.Never x p) := by
  unfold Pattern.Never NeverBits
  infer_instance

theorem Pattern.decode_code : ∀ t : Pattern, t.Valid → ofCode t.code = t := by decide

def Pattern.Closed3 (C : Finset (Fin 6)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C,
    (Pattern.med (ofCode u) (ofCode v) (ofCode w)).Valid

def Pattern.CommonNever (C : Finset (Fin 6)) : Prop :=
  ∃ x p : Fin 3, ∀ u ∈ C, (ofCode u).Never x p

instance (C : Finset (Fin 6)) : Decidable (Pattern.Closed3 C) := by
  unfold Pattern.Closed3
  infer_instance
instance (C : Finset (Fin 6)) : Decidable (Pattern.CommonNever C) := by
  unfold Pattern.CommonNever
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete six-order, three-alternative classification, checked by reduction
inside Lean's kernel. There are 64 subsets; no external enumeration is trusted. -/
theorem Pattern.finite_characterization :
    ∀ C : Finset (Fin 6), Pattern.Closed3 C → Pattern.CommonNever C := by decide

def orderPattern {α : Type*} (r : Order α) (a b c : α) : Pattern :=
  (r a b, r a c, r b c)

theorem orderPattern_valid {α : Type*} (r : Order α) {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) : (orderPattern r a b c).Valid := by
  constructor
  · exact fun h₁ h₂ => r.trans h₁ h₂
  · intro h₁ h₂
    have hba : r b a = true := (r.total hab).resolve_left (by simp [orderPattern] at h₁; simp [h₁])
    have hcb : r c b = true := (r.total hbc).resolve_left (by simp [orderPattern] at h₂; simp [h₂])
    exact r.asymmetric (r.trans hcb hba)

noncomputable def patternFamily {α : Type*} (D : Domain α) (a b c : α) : Finset (Fin 6) :=
  D.image (fun r => (orderPattern r a b c).code)

theorem patternFamily_closed {α : Type*} {D : Domain α} (hD : IsCondorcet D)
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) : Pattern.Closed3 (patternFamily D a b c) := by
  intro u hu v hv w hw
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
  rw [Pattern.decode_code _ (orderPattern_valid r hab hbc),
    Pattern.decode_code _ (orderPattern_valid s hab hbc),
    Pattern.decode_code _ (orderPattern_valid t hab hbc)]
  exact orderPattern_valid (medianOrder hD r s t hr hs ht) hab hbc

/-- Converse direction, with the finite triple classification fully checked. -/
theorem IsCondorcet.valueRestricted {α : Type*} {D : Domain α}
    (hD : IsCondorcet D) : ValueRestricted D := by
  classical
  intro a b c hab hac hbc
  obtain ⟨x, p, H⟩ := Pattern.finite_characterization _ (patternFamily_closed hD hab hbc)
  have hh : ∀ r ∈ D, (orderPattern r a b c).Never x p := by
    intro r hr
    have hcode : (orderPattern r a b c).code ∈ patternFamily D a b c :=
      Finset.mem_image.mpr ⟨r, hr, rfl⟩
    have ht := H _ hcode
    rwa [Pattern.decode_code _ (orderPattern_valid r hab hbc)] at ht
  refine ⟨p, ?_⟩
  fin_cases x
  · left
    intro r hr
    simpa [Pattern.Never, NeverBits, orderPattern, Never] using hh r hr
  · right; left
    intro r hr
    have ht := hh r hr
    simpa [Pattern.Never, NeverBits, orderPattern, Never,
      r.reverse_comparison hab] using ht
  · right; right
    intro r hr
    have ht := hh r hr
    simpa [Pattern.Never, NeverBits, orderPattern, Never,
      r.reverse_comparison hac, r.reverse_comparison hbc] using ht

theorem isCondorcet_iff_valueRestricted {α : Type*} (D : Domain α) :
    IsCondorcet D ↔ ValueRestricted D :=
  ⟨IsCondorcet.valueRestricted, ValueRestricted.isCondorcet⟩

#print axioms Pattern.finite_characterization
#print axioms IsCondorcet.valueRestricted
#print axioms isCondorcet_iff_valueRestricted
end Condorcet
