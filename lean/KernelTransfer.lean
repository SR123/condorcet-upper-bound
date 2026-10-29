import Std

/-!
A kernel-checked, standard-library-only arithmetic interface.
IMPORTANT: the named combinatorial hypotheses are theorem arguments.
This file isolates those hypotheses. The complete unconditional results for
actual Condorcet-domain extrema are stated and proved in CDCert.Main.
-/
namespace CondorcetUpperBounds

/-- Counts-based transfer after the component and gap theorems. -/
theorem deletion_transfer (positions M shadow gaps : Nat)
    (component : 3 * positions ≤ 8 * (shadow + gaps))
    (gap : gaps + positions + M ≤ 3 * shadow) :
    11 * positions + 8 * M ≤ 32 * shadow := by omega

/-- The paper's concrete one-step inequality, conditional on the three
explicit counting statements, with no division or approximate constants. -/
theorem general_recurrence (n M previous shadow gaps : Nat)
    (component : 3 * (n * M) ≤ 8 * (shadow + gaps))
    (gap : gaps + n * M + M ≤ 3 * shadow)
    (deletion : shadow ≤ n * previous) :
    (11 * n + 8) * M ≤ 32 * n * previous := by
  have h := deletion_transfer (n * M) M shadow gaps component gap
  have hs : 32 * shadow ≤ 32 * (n * previous) := Nat.mul_le_mul_left 32 deletion
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Interval-fibre case, again with density and deletion as explicit inputs. -/
theorem peak_pit_recurrence_scaled (n M previous shadow : Nat)
    (density : 3 * (n * M) ≤ 8 * shadow)
    (deletion : shadow ≤ n * previous) :
    3 * (n * M) ≤ 8 * (n * previous) := by omega

/-- Uniform boundary removal in its integer form. It is the exact scalar
consequence of applying an affine estimate to all ordered concatenations. -/
theorem remove_uniform_boundary (a b C : Nat)
    (copies : ∀ t : Nat, b * t ≤ a * t + C) : b ≤ a := by
  by_cases h : b ≤ a
  · exact h
  · have hab : a + 1 ≤ b := by omega
    have hm := Nat.mul_le_mul_right (C + 1) hab
    have hc := copies (C + 1)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    omega

/-- Exact iteration of a rational-rate recurrence, with denominators cleared. -/
theorem scaled_geometric_majorant (F : Nat → Nat) (den num base : Nat)
    (hbase : F 3 ≤ base)
    (hstep : ∀ k : Nat, den * F (k + 4) ≤ num * F (k + 3)) :
    ∀ k : Nat, den ^ k * F (k + 3) ≤ base * num ^ k := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have heq : k + 1 + 3 = k + 4 := by omega
    rw [heq]
    calc
      den ^ (k + 1) * F (k + 4) = den ^ k * (den * F (k + 4)) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ den ^ k * (num * F (k + 3)) := Nat.mul_le_mul_left _ (hstep k)
      _ = num * (den ^ k * F (k + 3)) := by
        simp only [Nat.mul_left_comm]
      _ ≤ num * (base * num ^ k) := Nat.mul_le_mul_left _ ih
      _ = base * num ^ (k + 1) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- Algebraic compression of the two boundary sums. The shared middle
slice equality is an explicit argument, not an assumed combinatorial axiom. -/
theorem potential_flow_compression (bb tb bt tt : Int) (middle : tb = bt) :
    bb - tb + bt - tt = (bb + tb) - (bt + tt) := by omega

/-- The finite sum of consecutive potential differences. -/
def potentialFlow (q : Nat → Int) : Nat → Int
  | 0 => 0
  | m + 1 => potentialFlow q m + q m - q (m + 1)

theorem potentialFlow_eq (q : Nat → Int) (m : Nat) :
    potentialFlow q m = q 0 - q m := by
  induction m with
  | zero => simp only [potentialFlow, Int.sub_self]
  | succ m ih =>
    simp only [potentialFlow]
    rw [ih]
    omega

theorem coefficient_identity : 12 * 8 = 5 * 19 + 1 := by decide

theorem seven_weight_numerator : 1 + 2 + 2 + 2 + 2 + 1 = 10 := by decide

#print axioms deletion_transfer
#print axioms general_recurrence
#print axioms peak_pit_recurrence_scaled
#print axioms remove_uniform_boundary
#print axioms scaled_geometric_majorant
#print axioms potential_flow_compression
#print axioms potentialFlow_eq
end CondorcetUpperBounds
