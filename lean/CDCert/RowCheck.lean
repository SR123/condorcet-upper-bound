/-
CDCert.RowCheck — kernel-sound exact integer row checking.

A certificate is an integer coefficient vector together with an integer
constant. A row is an integer feature vector. The residual of a row is

    residual c f = Σᵢ c.coeffs[i] * f[i] + c.const.

`checkRows c rows` is a Boolean function evaluated by the kernel (proved
`= true` by `decide`, never `native_decide`). Its soundness theorem says that
every row has exactly the certificate's length and a non-negative residual.
Length mismatches make the check fail; there is no silent truncation (a real
risk with `zipWith`-based dot products).

A rational certificate is covered by clearing denominators: multiplying the
coefficients and the constant by a positive common denominator does not
change the sign of any residual.

The aggregation lemmas turn "every local row has non-negative residual" into a
linear inequality for any sum of local feature vectors. `certified_inequality_of_cover`
is a CONDITIONAL bridge: its hypotheses `hcover` (every local configuration's
feature vector is one of the checked rows) and `hdecomp` (the global count
vector is the sum of the local feature vectors) are exactly what an
order-level formalisation still has to prove. Nothing here establishes them.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/

namespace CDCert.Rows

/-- Exact integer dot product; `none` on a length mismatch. -/
def dot? : List Int → List Int → Option Int
  | [], [] => some 0
  | a :: as, b :: bs => (dot? as bs).map (fun s => a * b + s)
  | [], _ :: _ => none
  | _ :: _, [] => none

/-- The mathematical dot product `Σ aᵢ bᵢ` (meaningful on equal lengths). -/
def dotSpec : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dotSpec as bs
  | _, _ => 0

theorem dot?_eq (a b : List Int) :
    dot? a b = if a.length = b.length then some (dotSpec a b) else none := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys =>
      show none = if 0 = ys.length + 1 then some (dotSpec [] (y :: ys)) else none
      rw [if_neg (fun h => Nat.succ_ne_zero _ h.symm)]
  | cons x xs ih =>
    cases b with
    | nil =>
      show none = if xs.length + 1 = 0 then some (dotSpec (x :: xs) []) else none
      rw [if_neg (Nat.succ_ne_zero _)]
    | cons y ys =>
      show (dot? xs ys).map (fun s => x * y + s) =
        if xs.length + 1 = ys.length + 1 then some (x * y + dotSpec xs ys) else none
      rw [ih ys]
      by_cases h : xs.length = ys.length
      · rw [if_pos h, if_pos (congrArg (· + 1) h)]
        rfl
      · rw [if_neg h, if_neg (fun h' => h (Nat.succ.inj h'))]
        rfl

theorem dot?_eq_some_iff {a b : List Int} {s : Int} :
    dot? a b = some s ↔ a.length = b.length ∧ dotSpec a b = s := by
  rw [dot?_eq]
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]

/-- A certificate: integer coefficients and an integer constant. -/
structure Cert where
  coeffs : List Int
  const : Int
deriving Repr

/-- The residual of a feature row (the quantity that must be non-negative). -/
def residual (c : Cert) (f : List Int) : Int := dotSpec c.coeffs f + c.const

/-- Check one row: correct length and non-negative residual, in exact integers. -/
def rowOK (c : Cert) (f : List Int) : Bool :=
  match dot? c.coeffs f with
  | some s => decide (0 ≤ s + c.const)
  | none => false

/-- Check every row. This is the Boolean the kernel evaluates. -/
def checkRows (c : Cert) (rows : List (List Int)) : Bool := rows.all (rowOK c)

theorem rowOK_eq_true {c : Cert} {f : List Int} :
    rowOK c f = true ↔ f.length = c.coeffs.length ∧ 0 ≤ residual c f := by
  unfold rowOK residual
  rw [dot?_eq]
  by_cases h : c.coeffs.length = f.length
  · simp only [if_pos h, decide_eq_true_eq]
    exact ⟨fun h' => ⟨h.symm, h'⟩, fun h' => h'.2⟩
  · simp only [if_neg h]
    constructor
    · intro h'
      cases h'
    · intro h'
      exact absurd h'.1.symm h

/-- **Soundness of the row check.** -/
theorem checkRows_sound {c : Cert} {rows : List (List Int)} (h : checkRows c rows = true) :
    ∀ f, f ∈ rows → f.length = c.coeffs.length ∧ 0 ≤ residual c f := by
  intro f hf
  exact rowOK_eq_true.mp (List.all_eq_true.mp h f hf)

/-- The check is also complete: it succeeds iff every row has the right length
and a non-negative residual. -/
theorem checkRows_iff {c : Cert} {rows : List (List Int)} :
    checkRows c rows = true ↔
      ∀ f, f ∈ rows → f.length = c.coeffs.length ∧ 0 ≤ residual c f := by
  unfold checkRows
  rw [List.all_eq_true]
  exact ⟨fun h f hf => rowOK_eq_true.mp (h f hf), fun h f hf => rowOK_eq_true.mpr (h f hf)⟩

/-! ### Aggregation -/

/-- Coordinatewise sum (used only on vectors of equal length). -/
def vadd : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: vadd as bs
  | _, _ => []

/-- Sum of a list of vectors, starting from the zero vector of length `k`. -/
def vsum (k : Nat) : List (List Int) → List Int
  | [] => List.replicate k 0
  | f :: fs => vadd f (vsum k fs)

theorem length_vadd : ∀ (a b : List Int), a.length = b.length → (vadd a b).length = a.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    simp only [vadd, List.length_cons] at h ⊢
    rw [length_vadd as bs (Nat.succ.inj h)]

theorem length_vsum (k : Nat) (fs : List (List Int)) (h : ∀ f, f ∈ fs → f.length = k) :
    (vsum k fs).length = k := by
  induction fs with
  | nil => simp [vsum]
  | cons f fs ih =>
    have hf := h f List.mem_cons_self
    have ih' := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [vsum]
    rw [length_vadd f (vsum k fs) (by rw [hf, ih']), hf]

theorem dotSpec_vadd : ∀ (c a b : List Int), a.length = c.length → b.length = c.length →
    dotSpec c (vadd a b) = dotSpec c a + dotSpec c b
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, ha, _ => by cases ha
  | [], [], _ :: _, _, hb => by cases hb
  | _ :: _, [], _, ha, _ => by cases ha
  | _ :: _, _ :: _, [], _, hb => by cases hb
  | x :: cs, a :: as, b :: bs, ha, hb => by
    simp only [List.length_cons] at ha hb
    simp only [vadd, dotSpec]
    rw [dotSpec_vadd cs as bs (Nat.succ.inj ha) (Nat.succ.inj hb), Int.mul_add]
    omega

theorem dotSpec_replicate_zero : ∀ (c : List Int) (k : Nat), dotSpec c (List.replicate k 0) = 0
  | [], _ => by cases ‹Nat› <;> rfl
  | _ :: _, 0 => rfl
  | x :: cs, k + 1 => by
    simp only [List.replicate_succ, dotSpec, Int.mul_zero, dotSpec_replicate_zero cs k]
    rfl

/-- Linearity: the dot product with a sum of rows is the sum of dot products. -/
theorem dotSpec_vsum (c : List Int) (fs : List (List Int))
    (h : ∀ f, f ∈ fs → f.length = c.length) :
    dotSpec c (vsum c.length fs) = (fs.map (dotSpec c)).sum := by
  induction fs with
  | nil => simp [vsum, dotSpec_replicate_zero]
  | cons f fs ih =>
    have hf := h f List.mem_cons_self
    have hfs : ∀ g, g ∈ fs → g.length = c.length := fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [vsum, List.map_cons, List.sum_cons]
    rw [dotSpec_vadd c f (vsum c.length fs) hf (length_vsum _ fs hfs), ih hfs]

theorem sum_map_residual (c : Cert) (fs : List (List Int))
    (h : ∀ f, f ∈ fs → f.length = c.coeffs.length) :
    (fs.map (residual c)).sum =
      dotSpec c.coeffs (vsum c.coeffs.length fs) + (fs.length : Int) * c.const := by
  rw [dotSpec_vsum c.coeffs fs h]
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have ih' := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [List.map_cons, List.sum_cons, List.length_cons, residual]
    rw [ih', Int.natCast_add, Int.add_mul]
    omega

theorem sum_nonneg_of_forall {l : List Int} (h : ∀ x, x ∈ l → 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

/-- **Aggregation.** If the row check passes, then for any finite list `fs` of
checked rows (repetitions allowed, i.e. with multiplicities) the summed linear
inequality holds. -/
theorem certified_sum_nonneg {c : Cert} {rows : List (List Int)}
    (hcheck : checkRows c rows = true) (fs : List (List Int))
    (hfs : ∀ f, f ∈ fs → f ∈ rows) :
    0 ≤ dotSpec c.coeffs (vsum c.coeffs.length fs) + (fs.length : Int) * c.const := by
  have hok := checkRows_sound hcheck
  have hlen : ∀ f, f ∈ fs → f.length = c.coeffs.length := fun f hf => (hok f (hfs f hf)).1
  rw [← sum_map_residual c fs hlen]
  apply sum_nonneg_of_forall
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  exact (hok f (hfs f hf)).2

/-- **Conditional bridge (NOT a proof of the semantic connection).**
Suppose the row check passes. If
* `hcover`: every local configuration `x` in `locals` has its feature vector
  `feat x` among the checked rows, and
* `hdecomp`: the global count vector `glob` is the sum of the local feature
  vectors,
then the certified linear inequality holds for `glob`. Both hypotheses must be
proved at the level of actual orders and domains; see the report. -/
theorem certified_inequality_of_cover {ι : Type} {c : Cert} {rows : List (List Int)}
    (hcheck : checkRows c rows = true) (locals : List ι) (feat : ι → List Int)
    (hcover : ∀ x, x ∈ locals → feat x ∈ rows) (glob : List Int)
    (hdecomp : glob = vsum c.coeffs.length (locals.map feat)) :
    0 ≤ dotSpec c.coeffs glob + (locals.length : Int) * c.const := by
  have h := certified_sum_nonneg hcheck (locals.map feat) (by
    intro f hf
    rw [List.mem_map] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    exact hcover x hx)
  rw [List.length_map] at h
  rw [hdecomp]
  exact h

end CDCert.Rows
