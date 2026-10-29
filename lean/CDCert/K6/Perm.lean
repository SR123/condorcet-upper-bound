/-
CDCert.K6.Perm — permutations of labels as lists, acting on orders.

A permutation of `0..n-1` is a list `σ ∈ orders n`; it acts on labels by
`app σ a = σ.getD a a` (so labels `≥ n` are fixed) and on orders by `rlab σ`
(`CDCert.K6.Defs5`).

* `app_injective`, `app_lt_iff`, `app_of_ge`, `exists_app_eq`: `app σ` is a
  bijection of `ℕ` preserving `0..n-1`;
* `pinv n σ`: the inverse permutation, `app_pinv_app`, `app_app_pinv`, `pinv_mem_orders`;
* `rlab_mem_orders`, `rlab_pinv_rlab`, `rlab_rlab_pinv`: action on orders;
* `before_rlab`: comparisons are transported;
* `rlab_comp`: composition;
* `restrictTo_rlab`, `restrictTo_eq_deleteLabel`: restriction to `0..k-1` commutes
  with permutations of `0..k-1`, and on `orders (k+1)` it is deletion of `k`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs5
import CDCert.Deletion
import CDCert.Extension

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-- Action on labels. -/
def app (σ : List Nat) (a : Nat) : Nat := σ.getD a a

theorem rlab_eq_map (σ L : List Nat) : rlab σ L = L.map (app σ) := rfl

section
variable {n : Nat} {σ : List Nat}

theorem length_of_mem_orders (h : σ ∈ orders n) : σ.length = n := by
  rw [(mem_orders_iff.mp h).length_eq, List.length_range]

theorem getD_of_lt {l : List Nat} {i d : Nat} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_of_ge {l : List Nat} {i d : Nat} (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getElem_idxOf_of_mem : ∀ {l : List Nat} {a : Nat} (h : a ∈ l),
    l[l.idxOf a]'(List.idxOf_lt_length_iff.mpr h) = a
  | b :: l, a, h => by
    by_cases hb : b = a
    · subst hb
      simp
    · have hmem : a ∈ l := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hb
        · exact h'
      have hidx : (b :: l).idxOf a = l.idxOf a + 1 := by
        rw [List.idxOf_cons]
        have hba : (b == a) = false := by rw [beq_eq_false_iff_ne]; exact hb
        rw [hba]
        rfl
      simp only [hidx, List.getElem_cons_succ]
      exact getElem_idxOf_of_mem hmem

theorem nodup_getElem_inj {l : List Nat} (hnd : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (h : l[i] = l[j]) : i = j := by
  have hp := List.pairwise_iff_getElem.mp hnd
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (hp i j hi hj hij)
  · exact hij
  · exact absurd h.symm (hp j i hj hi hij)

theorem app_of_lt (h : σ ∈ orders n) {a : Nat} (ha : a < n) :
    app σ a = σ[a]'(by rw [length_of_mem_orders h]; exact ha) := by
  unfold app
  exact getD_of_lt _

theorem app_of_ge (h : σ ∈ orders n) {a : Nat} (ha : n ≤ a) : app σ a = a := by
  unfold app
  exact getD_of_ge (by rw [length_of_mem_orders h]; exact ha)

theorem app_lt (h : σ ∈ orders n) {a : Nat} (ha : a < n) : app σ a < n := by
  rw [app_of_lt h ha]
  exact (mem_of_mem_orders h _).mp (List.getElem_mem _)

theorem app_lt_iff (h : σ ∈ orders n) (a : Nat) : app σ a < n ↔ a < n := by
  constructor
  · intro h'
    rcases Nat.lt_or_ge a n with ha | ha
    · exact ha
    · rw [app_of_ge h ha] at h'
      exact absurd h' (by omega)
  · exact app_lt h

theorem app_injective (h : σ ∈ orders n) : Function.Injective (app σ) := by
  intro a b hab
  have hnd := nodup_of_mem_orders h
  have hlen := length_of_mem_orders h
  by_cases ha : a < n <;> by_cases hb : b < n
  · rw [app_of_lt h ha, app_of_lt h hb] at hab
    exact nodup_getElem_inj hnd _ _ hab
  · rw [app_of_ge h (a := b) (by omega)] at hab
    have := app_lt h ha
    rw [hab] at this
    exact absurd this hb
  · rw [app_of_ge h (a := a) (by omega)] at hab
    have := app_lt h hb
    rw [← hab] at this
    exact absurd this ha
  · rw [app_of_ge h (by omega), app_of_ge h (by omega)] at hab
    exact hab

theorem exists_app_eq (h : σ ∈ orders n) {b : Nat} (hb : b < n) : ∃ a, a < n ∧ app σ a = b := by
  have hmem : b ∈ σ := (mem_of_mem_orders h b).mpr hb
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hmem
  have hlen := length_of_mem_orders h
  refine ⟨a, by omega, ?_⟩
  rw [app_of_lt h (by omega)]

/-- The inverse permutation. -/
def pinv (n : Nat) (σ : List Nat) : List Nat := (List.range n).map (fun b => σ.idxOf b)

theorem app_pinv_of_lt (h : σ ∈ orders n) {b : Nat} (hb : b < n) : app (pinv n σ) b = σ.idxOf b := by
  unfold app pinv
  rw [getD_of_lt (by rw [List.length_map, List.length_range]; exact hb)]
  simp

theorem app_app_pinv (h : σ ∈ orders n) (b : Nat) : app σ (app (pinv n σ) b) = b := by
  by_cases hb : b < n
  · rw [app_pinv_of_lt h hb]
    have hmem : b ∈ σ := (mem_of_mem_orders h b).mpr hb
    have hi : σ.idxOf b < σ.length := List.idxOf_lt_length_iff.mpr hmem
    rw [app_of_lt h (by rw [← length_of_mem_orders h]; exact hi)]
    exact getElem_idxOf_of_mem hmem
  · have hp : app (pinv n σ) b = b := by
      unfold app pinv
      exact getD_of_ge (by rw [List.length_map, List.length_range]; omega)
    rw [hp, app_of_ge h (by omega)]

theorem app_pinv_app (h : σ ∈ orders n) (a : Nat) : app (pinv n σ) (app σ a) = a :=
  app_injective h (app_app_pinv h (app σ a))

theorem pinv_mem_orders (h : σ ∈ orders n) : pinv n σ ∈ orders n := by
  rw [mem_orders_iff]
  apply perm_of_nodup_of_mem_iff
  · unfold pinv
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => ?_) List.nodup_range
    intro heq
    have := congrArg (app σ) (show app (pinv n σ) x = app (pinv n σ) y by
      rw [app_pinv_of_lt h (List.mem_range.mp hx), app_pinv_of_lt h (List.mem_range.mp hy)]
      exact heq)
    rw [app_app_pinv h, app_app_pinv h] at this
    exact hxy this
  · exact List.nodup_range
  · intro a
    rw [List.mem_range]
    unfold pinv
    rw [List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' := List.mem_range.mp hb
      have hmem : b ∈ σ := (mem_of_mem_orders h b).mpr hb'
      have hi : σ.idxOf b < σ.length := List.idxOf_lt_length_iff.mpr hmem
      rw [length_of_mem_orders h] at hi
      exact hi
    · intro ha
      refine ⟨app σ a, List.mem_range.mpr (app_lt h ha), ?_⟩
      have := app_pinv_app h a
      rw [app_pinv_of_lt h (app_lt h ha)] at this
      exact this

theorem rlab_mem_orders (h : σ ∈ orders n) {L : List Nat} (hL : L ∈ orders n) :
    rlab σ L ∈ orders n := by
  rw [mem_orders_iff] at hL ⊢
  rw [rlab_eq_map]
  refine (hL.map (app σ)).trans ?_
  have : (List.range n).map (app σ) = σ := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, length_of_mem_orders h]
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      rw [List.length_map, List.length_range] at h1
      rw [app_of_lt h h1]
  rw [this]
  exact mem_orders_iff.mp h

theorem rlab_pinv_rlab (h : σ ∈ orders n) (L : List Nat) : rlab (pinv n σ) (rlab σ L) = L := by
  rw [rlab_eq_map, rlab_eq_map, List.map_map]
  conv => rhs; rw [← List.map_id L]
  apply List.map_congr_left
  intro a _
  exact app_pinv_app h a

theorem rlab_rlab_pinv (h : σ ∈ orders n) (L : List Nat) : rlab σ (rlab (pinv n σ) L) = L := by
  rw [rlab_eq_map, rlab_eq_map, List.map_map]
  conv => rhs; rw [← List.map_id L]
  apply List.map_congr_left
  intro a _
  exact app_app_pinv h a

theorem before_rlab (h : σ ∈ orders n) (a b : Nat) (L : List Nat) :
    before (app σ a) (app σ b) (rlab σ L) = before a b L := by
  rw [rlab_eq_map]
  exact before_map (app σ) (app_injective h) a b L

end

/-- Composition: `rlab σ ∘ rlab τ = rlab (τ.map (app σ))` for permutations of `0..n-1`. -/
theorem app_comp {n : Nat} {σ τ : List Nat} (hσ : σ ∈ orders n) (hτ : τ ∈ orders n) (a : Nat) :
    app (τ.map (app σ)) a = app σ (app τ a) := by
  by_cases ha : a < n
  · have hlen : (τ.map (app σ)).length = n := by rw [List.length_map, length_of_mem_orders hτ]
    show (τ.map (app σ)).getD a a = app σ (app τ a)
    rw [getD_of_lt (by rw [hlen]; exact ha), List.getElem_map, app_of_lt hτ ha]
  · have h1 : app (τ.map (app σ)) a = a := by
      unfold app
      exact getD_of_ge (by rw [List.length_map, length_of_mem_orders hτ]; omega)
    rw [h1, app_of_ge hτ (by omega), app_of_ge hσ (by omega)]

theorem comp_mem_orders {n : Nat} {σ τ : List Nat} (hσ : σ ∈ orders n) (hτ : τ ∈ orders n) :
    τ.map (app σ) ∈ orders n := by
  have := rlab_mem_orders hσ hτ
  rwa [rlab_eq_map] at this

theorem rlab_comp {n : Nat} {σ τ : List Nat} (hσ : σ ∈ orders n) (hτ : τ ∈ orders n) (L : List Nat) :
    rlab σ (rlab τ L) = rlab (τ.map (app σ)) L := by
  rw [rlab_eq_map, rlab_eq_map, rlab_eq_map, List.map_map]
  apply List.map_congr_left
  intro a _
  exact (app_comp hσ hτ a).symm

/-- Permutations of `0..k-1` commute with restriction to `0..k-1`. -/
theorem restrictTo_rlab {k : Nat} {σ : List Nat} (h : σ ∈ orders k) (L : List Nat) :
    restrictTo k (rlab σ L) = rlab σ (restrictTo k L) := by
  unfold restrictTo
  rw [rlab_eq_map, rlab_eq_map, List.filter_map]
  congr 1
  apply List.filter_congr
  intro a _
  simp only [Function.comp, app_lt_iff h a]

/-- On orders of `0..k`, restriction to `0..k-1` is deletion of `k`. -/
theorem restrictTo_eq_deleteLabel {k : Nat} {L : List Nat} (hL : L ∈ orders (k + 1)) :
    restrictTo k L = deleteLabel k L := by
  unfold restrictTo deleteLabel
  have h1 : L.filter (fun a => decide (a < k)) = L.filter (fun a => a != k) := by
    apply List.filter_congr
    intro a ha
    have := (mem_of_mem_orders hL a).mp ha
    by_cases hak : a = k
    · subst hak; simp
    · have : a < k := by omega
      simp [this, hak]
  rw [h1]
  conv => lhs; rw [← List.map_id (L.filter (fun a => a != k))]
  apply List.map_congr_left
  intro a ha
  rw [List.mem_filter] at ha
  have := (mem_of_mem_orders hL a).mp ha.1
  have hak : a ≠ k := by simpa using ha.2
  unfold down
  rw [if_pos (by omega)]
  rfl

end CDCert.K6
