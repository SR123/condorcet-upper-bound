/-
CDCert.K6.Theta — the potential of the finite lemma, at list level and scaled by `2D`
(`D = 8846117280`, all quantities integers), and the **compressed identity**.

For a six-domain `H` (predicate on orders of `0..5`):
* `potW p = |p| · D φ(p)` for a five-domain (`φ` read from the five-table by type);
* `bD H = D b(H)`, `tD H = D t(H)`: sums of `potW` over the bottom / top five-slices;
* `rb H`, `rt H`: numbers of bottom five-slices of type 866, top five-slices of type 41;
* `sD H = D s(H) = K|H| + bD − tD − (D/5) A(H)`, with `K = 12D/19`, `A = adj 6`;
* `IsS H`: `H` is a relabelling of one of the nine S types `excRep6.getD i 0` (`i < 9`),
  `sIdx H` such an `i`, `psiD i = 2Dψ_i`;
* `pD H = 2D p(H)`: `psiD (sIdx H)` on S, `4ηD (r_t − r_b)` otherwise;
* `thB = sD + pD = 2D θ_b`, `thT = sD − pD = 2D θ_t`, `qD = bD + tD + pD = 2D q`;
* `lamD J = 2D Λ(J) = Σ_z thB (B_z J) + Σ_w thT (T_w J)` for a seven-domain `J`.

Results:
* `topP_botP`: a top slice of a bottom slice is a bottom slice of a top slice;
* `sum_tD_bot`: `Σ_z tD (B_z J) = Σ_w bD (T_w J)` ("the middle terms cancel");
* **`lamD_eq`**: `lamD J = 2K|J| − (D/5)·10C(J) + Σ_z qD (B_z J) − Σ_w qD (T_w J)`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.TabSemB
import CDCert.K6.Seven.Data

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

/-! ### Six-domains from masks, and isomorphism types -/

/-- The six-domain with bottom-indexed mask `m` over `baseB 5`. -/
def memB6 (m : Nat) (M : List Nat) : Bool := m.testBit (idx6 M)

/-- `H` is a relabelling of the six-domain with mask `m`. -/
def IsoM (m : Nat) (H : List Nat → Bool) : Prop :=
  ∃ σ, σ ∈ orders 6 ∧ ∀ M, M ∈ orders 6 → H M = memB6 m (rlab σ M)

/-- `H` has one of the nine S types. -/
def IsS (H : List Nat → Bool) : Prop := ∃ i, i < 9 ∧ IsoM (excRep6.getD i 0) H

/-- An S type of `H` (unique, see `CDCert.K6.SevenKeys`). -/
noncomputable def sIdx (H : List Nat → Bool) : Nat :=
  @dite _ (IsS H) (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => 0)

theorem sIdx_spec {H : List Nat → Bool} (h : IsS H) : sIdx H < 9 ∧ IsoM (excRep6.getD (sIdx H) 0) H := by
  unfold sIdx
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- `2Dψ` of the S type `i`. -/
noncomputable def psiD (i : Nat) : Int := (psiT.find i : Int) - 2 ^ 62

/-! ### The potential -/

/-- `|p| · D φ(p)` for a five-domain. -/
noncomputable def potW (p : List Nat → Bool) : Int := (card 5 p : Int) * pot5 (ty5 p)

/-- `1` if the five-domain is nonempty and of type `k`. -/
noncomputable def isTy (k : Nat) (p : List Nat → Bool) : Nat := if card 5 p ≠ 0 ∧ ty5 p = k then 1 else 0

/-- `D b(H)`. -/
noncomputable def bD (H : List Nat → Bool) : Int := ((List.range 6).map (fun x => potW (botP x H))).sum
/-- `D t(H)`. -/
noncomputable def tD (H : List Nat → Bool) : Int := ((List.range 6).map (fun y => potW (topP y H))).sum
/-- `r_b(H)`: bottom five-slices of type 866 (`R₈` with its first alternative deleted). -/
noncomputable def rb (H : List Nat → Bool) : Nat := ((List.range 6).map (fun x => isTy 866 (botP x H))).sum
/-- `r_t(H)`: top five-slices of type 41 (`R₈` with its last alternative deleted). -/
noncomputable def rt (H : List Nat → Bool) : Nat := ((List.range 6).map (fun y => isTy 41 (topP y H))).sum

/-- `D s(H) = K|H| + D b(H) − D t(H) − (D/5) A(H)`. -/
noncomputable def sD (H : List Nat → Bool) : Int :=
  (cK : Int) * card 6 H + bD H - tD H - (cD5 : Int) * adj 6 H

/-- `2D p(H)`. -/
noncomputable def pD (H : List Nat → Bool) : Int :=
  @ite _ (IsS H) (Classical.propDecidable _) (psiD (sIdx H)) (4 * (cE : Int) * ((rt H : Int) - rb H))

/-- `2D θ_b(H)`. -/
noncomputable def thB (H : List Nat → Bool) : Int := sD H + pD H
/-- `2D θ_t(H)`. -/
noncomputable def thT (H : List Nat → Bool) : Int := sD H - pD H
/-- `2D q(H)`, `q = (b + t)/2 + p`. -/
noncomputable def qD (H : List Nat → Bool) : Int := bD H + tD H + pD H

/-- `2D Λ(J)` of a seven-domain. -/
noncomputable def lamD (J : List Nat → Bool) : Int :=
  ((List.range 7).map (fun z => thB (botP z J))).sum + ((List.range 7).map (fun w => thT (topP w J))).sum

/-! ### Integer sums -/

theorem isum_append (l₁ l₂ : List Int) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.sum_cons, ih]; omega

theorem isum_map_add {α : Type} (l : List α) (f g : α → Int) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem isum_map_sub {α : Type} (l : List α) (f g : α → Int) :
    (l.map (fun a => f a - g a)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem isum_map_mul {α : Type} (l : List α) (c : Int) (f : α → Int) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem isum_cast {α : Type} (l : List α) (f : α → Nat) :
    (l.map (fun a => (f a : Int))).sum = ((l.map f).sum : Nat) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Int.natCast_add]

theorem isum_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → Int) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, isum_append, ih, List.map_cons, List.sum_cons]

/-! ### Slices of slices -/

theorem up_up_eq (z y a : Nat) : up z (up y a) = up (up z y) (up (down (up z y) z) a) := by
  unfold up down
  by_cases h1 : a < y <;> by_cases h2 : y < z <;> simp only [h1, h2, if_true, if_false] <;>
    (repeat' split) <;> omega

theorem up_down_up (z y : Nat) : up (up z y) (down (up z y) z) = z :=
  up_down (Ne.symm (up_ne z y))

/-- **A top slice of a bottom slice is a bottom slice of a top slice.** -/
theorem topP_botP (z y : Nat) (J : List Nat → Bool) :
    topP y (botP z J) = botP (down (up z y) z) (topP (up z y) J) := by
  funext L
  show J (gB z (gT y L)) = J (gT (up z y) (gB (down (up z y) z) L))
  unfold gB gT
  congr 1
  simp only [List.map_cons, List.map_append, List.map_map, List.cons_append, List.map_nil]
  rw [up_down_up]
  congr 2
  apply List.map_congr_left
  intro a _
  exact up_up_eq z y a

/-- Pairs `(z, y)`, `z < 7`, `y < 6`. -/
def pairs76 : List (Nat × Nat) := (List.range 7).flatMap (fun z => (List.range 6).map (fun y => (z, y)))

theorem perm_pairs76 : (pairs76.map (fun p => (up p.1 p.2, down (up p.1 p.2) p.1))).Perm pairs76 := by
  decide

theorem isum_pairs76 (h : Nat → Nat → Int) :
    ((List.range 7).map (fun z => ((List.range 6).map (fun y => h z y)).sum)).sum =
      (pairs76.map (fun p => h p.1 p.2)).sum := by
  unfold pairs76
  rw [isum_flatMap]
  congr 1

/-- **The middle terms cancel.** -/
theorem sum_tD_bot (J : List Nat → Bool) :
    ((List.range 7).map (fun z => tD (botP z J))).sum = ((List.range 7).map (fun w => bD (topP w J))).sum := by
  unfold tD bD
  rw [isum_pairs76 (fun z y => potW (topP y (botP z J))), isum_pairs76 (fun w x => potW (botP x (topP w J)))]
  simp only [topP_botP]
  have := perm_sum_int (perm_pairs76.map (fun p => potW (botP p.2 (topP p.1 J))))
  rw [List.map_map] at this
  exact this

/-- **The compressed identity.** -/
theorem lamD_eq (J : List Nat → Bool) :
    lamD J = 2 * ((cK : Int) * card 7 J) - (cD5 : Int) * cost10 J +
      ((List.range 7).map (fun z => qD (botP z J))).sum - ((List.range 7).map (fun w => qD (topP w J))).sum := by
  have hcb : ((List.range 7).map (fun z => (card 6 (botP z J) : Int))).sum = card 7 J := by
    rw [isum_cast, ← card_succ_bot]
  have hct : ((List.range 7).map (fun w => (card 6 (topP w J) : Int))).sum = card 7 J := by
    rw [isum_cast, ← card_succ_top]
  have hc10 : ((List.range 7).map (fun z => (adj 6 (botP z J) : Int))).sum +
      ((List.range 7).map (fun w => (adj 6 (topP w J) : Int))).sum = cost10 J := by
    rw [isum_cast, isum_cast, cost10_split, Int.natCast_add]
  have hmid := sum_tD_bot J
  have hsb : ((List.range 7).map (fun z => sD (botP z J))).sum =
      (cK : Int) * ((List.range 7).map (fun z => (card 6 (botP z J) : Int))).sum +
      ((List.range 7).map (fun z => bD (botP z J))).sum - ((List.range 7).map (fun z => tD (botP z J))).sum -
      (cD5 : Int) * ((List.range 7).map (fun z => (adj 6 (botP z J) : Int))).sum := by
    unfold sD
    rw [isum_map_sub, isum_map_sub, isum_map_add, isum_map_mul, isum_map_mul]
  have hst : ((List.range 7).map (fun w => sD (topP w J))).sum =
      (cK : Int) * ((List.range 7).map (fun w => (card 6 (topP w J) : Int))).sum +
      ((List.range 7).map (fun w => bD (topP w J))).sum - ((List.range 7).map (fun w => tD (topP w J))).sum -
      (cD5 : Int) * ((List.range 7).map (fun w => (adj 6 (topP w J) : Int))).sum := by
    unfold sD
    rw [isum_map_sub, isum_map_sub, isum_map_add, isum_map_mul, isum_map_mul]
  have hl : lamD J = ((List.range 7).map (fun z => sD (botP z J))).sum + ((List.range 7).map (fun z => pD (botP z J))).sum +
      (((List.range 7).map (fun w => sD (topP w J))).sum - ((List.range 7).map (fun w => pD (topP w J))).sum) := by
    unfold lamD thB thT
    rw [isum_map_add, isum_map_sub]
  have hqb : ((List.range 7).map (fun z => qD (botP z J))).sum =
      ((List.range 7).map (fun z => bD (botP z J))).sum + ((List.range 7).map (fun z => tD (botP z J))).sum +
      ((List.range 7).map (fun z => pD (botP z J))).sum := by
    unfold qD; rw [isum_map_add, isum_map_add]
  have hqt : ((List.range 7).map (fun w => qD (topP w J))).sum =
      ((List.range 7).map (fun w => bD (topP w J))).sum + ((List.range 7).map (fun w => tD (topP w J))).sum +
      ((List.range 7).map (fun w => pD (topP w J))).sum := by
    unfold qD; rw [isum_map_add, isum_map_add]
  rw [hcb] at hsb
  rw [hct] at hst
  have hK : (cK : Int) = 5587021440 := rfl
  have hD : (cD5 : Int) = 1769223456 := rfl
  rw [hK, hD] at hsb hst ⊢
  rw [hl, hqb, hqt, hsb, hst, ← hc10]
  omega

end CDCert.K6
