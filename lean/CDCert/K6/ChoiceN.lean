/-
CDCert.K6.ChoiceN — choices for `groupsEP n` described by a law per triple and an
optional comparison per pair (core-only copy of the list-level part of
`CDCert.BridgeEP`, in namespace `CDCert.K6`; the statements and proofs are the
same, so the Mathlib-side bridge is unchanged).

* `choiceEPN lawN pairN k`, `allows_choiceEPN`: the choice and its solution condition;
* `isChoice_groupsEP_iff`: every choice for `groupsEP n` is `choiceEPN lawN pairN n`
  for an extreme `lawN`; `isChoice_choiceEPN`: conversely.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Extension

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

theorem isChoice_map_map {ι ω : Type} (f : ι → ω) (g : ι → List ω) :
    ∀ (l : List ι), (∀ i, i ∈ l → f i ∈ g i) → IsChoice (l.map f) (l.map g)
  | [], _ => IsChoice.nil
  | i :: l, h =>
    IsChoice.cons (h i List.mem_cons_self)
      (isChoice_map_map f g l (fun j hj => h j (List.mem_cons_of_mem _ hj)))


/-! ### Nat-level choices for `groupsEP` -/

/-- The option chosen for the pair `(a, c)`: no constraint, `a` above `c`
(`some true`, as `Condorcet.encode`), or `c` above `a` (`some false`). -/
def pairChoice (a c : Nat) : Option Bool → Opt (List Nat)
  | none => fun _ => true
  | some true => pairL a c
  | some false => pairL c a

theorem pairChoice_mem (a c : Nat) : ∀ o : Option Bool, pairChoice a c o ∈ pairOptions a c
  | none => List.mem_cons_self
  | some true => List.mem_cons_of_mem _ List.mem_cons_self
  | some false => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Options introduced with label `k`, in the order of `groupsNew k`. -/
def choiceNew (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool)
    (k : Nat) : List (Opt (List Nat)) :=
  (newTriples k).map (fun t => holdsL t.1 t.2.1 t.2.2 (lawN t)) ++
  (List.range k).map (fun a => pairChoice a k (pairN a k))

/-- The choice for `groupsEP k`, built label by label like `groupsEP`. -/
def choiceEPN (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool) :
    Nat → List (Opt (List Nat))
  | 0 => []
  | k + 1 => choiceEPN lawN pairN k ++ choiceNew lawN pairN k

theorem mem_lawsExtreme : ∀ law : Fin 3 × Fin 3, law.2 ≠ 1 → law ∈ lawsExtreme := by
  intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
  have h1 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb1 : b ≠ 1 := fun e => h (Fin.ext e)
  have h2 : b = 0 ∨ b = 2 := by omega
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl <;>
    simp [lawsExtreme, Prod.ext_iff, Fin.ext_iff]

theorem ne_one_of_mem_lawsExtreme : ∀ law : Fin 3 × Fin 3, law ∈ lawsExtreme → law.2 ≠ 1 := by
  intro law h
  simp only [lawsExtreme, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem isChoice_choiceNew (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    (pairN : Nat → Nat → Option Bool) (k : Nat)
    (hlaw : ∀ t, t ∈ newTriples k → lawN t ∈ lawsExtreme) :
    IsChoice (choiceNew lawN pairN k) (groupsNew k) :=
  isChoice_append.mpr ⟨_, _, rfl,
    isChoice_map_map _ _ _ (fun t ht => List.mem_map_of_mem (hlaw t ht)),
    isChoice_map_map _ _ _ (fun a _ => pairChoice_mem a k _)⟩

theorem isChoice_choiceEPN (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    (pairN : Nat → Nat → Option Bool) :
    ∀ k, (∀ j t, j < k → t ∈ newTriples j → lawN t ∈ lawsExtreme) →
      IsChoice (choiceEPN lawN pairN k) (groupsEP k)
  | 0, _ => IsChoice.nil
  | k + 1, h => isChoice_append.mpr ⟨_, _, rfl,
      isChoice_choiceEPN lawN pairN k (fun j t hj ht => h j t (by omega) ht),
      isChoice_choiceNew lawN pairN k (fun t ht => h k t (by omega) ht)⟩

/-! ### The solution condition of `choiceEPN` -/

theorem allows_append (c₁ c₂ : List (Opt (List Nat))) (x : List Nat) :
    allows (c₁ ++ c₂) x = (allows c₁ x && allows c₂ x) := by
  simp only [allows, List.all_append]

theorem allows_choiceNew (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    (pairN : Nat → Nat → Option Bool) (k : Nat) (x : List Nat) :
    allows (choiceNew lawN pairN k) x = true ↔
      (∀ t, t ∈ newTriples k → holdsL t.1 t.2.1 t.2.2 (lawN t) x = true) ∧
      (∀ a, a < k → pairChoice a k (pairN a k) x = true) := by
  unfold choiceNew
  rw [allows_append, Bool.and_eq_true, allows_eq_true, allows_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun t ht => h1 _ (List.mem_map_of_mem ht),
      fun a ha => h2 _ (List.mem_map_of_mem (List.mem_range.mpr ha))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun o ho => ?_, fun o ho => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
      exact h1 t ht
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
      exact h2 a (List.mem_range.mp ha)

/-- **Solution condition.** -/
theorem allows_choiceEPN (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    (pairN : Nat → Nat → Option Bool) (x : List Nat) :
    ∀ k, allows (choiceEPN lawN pairN k) x = true ↔
      (∀ t, t ∈ triplesN k → holdsL t.1 t.2.1 t.2.2 (lawN t) x = true) ∧
      (∀ a c, a < c → c < k → pairChoice a c (pairN a c) x = true)
  | 0 => by
    simp only [choiceEPN, allows, List.all_nil, true_iff]
    exact ⟨fun t ht => absurd (mem_triplesN.mp ht).2.2 (Nat.not_lt_zero _),
      fun a c _ hc => absurd hc (Nat.not_lt_zero _)⟩
  | k + 1 => by
    have ih := allows_choiceEPN lawN pairN x k
    rw [show choiceEPN lawN pairN (k + 1) = choiceEPN lawN pairN k ++ choiceNew lawN pairN k
      from rfl, allows_append, Bool.and_eq_true, ih, allows_choiceNew]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨fun t ht => ?_, fun a c hac hc => ?_⟩
      · obtain ⟨t1, t2, t3⟩ := mem_triplesN.mp ht
        by_cases h : t.2.2 < k
        · exact h1 t (mem_triplesN.mpr ⟨t1, t2, h⟩)
        · exact h3 t (mem_newTriples.mpr ⟨t1, by omega, by omega⟩)
      · by_cases h : c < k
        · exact h2 a c hac h
        · have hck : c = k := by omega
          subst hck
          exact h4 a hac
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun t ht => h1 t ?_, fun a c hac hc => h2 a c hac (by omega)⟩,
        fun t ht => h1 t ?_, fun a ha => h2 a k ha (by omega)⟩
      · obtain ⟨t1, t2, t3⟩ := mem_triplesN.mp ht
        exact mem_triplesN.mpr ⟨t1, t2, by omega⟩
      · obtain ⟨t1, t2, t3⟩ := mem_newTriples.mp ht
        exact mem_triplesN.mpr ⟨t1, by omega, by omega⟩

/-! ### Every choice for `groupsEP n` comes from laws and pairs -/

/-- Choices for a list of groups indexed by `l` whose group at `i` is `(A i).map (F i)`. -/
theorem isChoice_map_iff {ι α : Type} [DecidableEq ι] [Inhabited α] (F : ι → α → Opt (List Nat))
    (A : ι → List α) :
    ∀ (l : List ι), l.Nodup → ∀ (c : List (Opt (List Nat))),
      IsChoice c (l.map (fun i => (A i).map (F i))) →
        ∃ f : ι → α, (∀ i, i ∈ l → f i ∈ A i) ∧ c = l.map (fun i => F i (f i))
  | [], _, c, h => by
    rw [List.map_nil, isChoice_nil_iff] at h
    subst h
    exact ⟨fun _ => default, fun _ hi => absurd hi List.not_mem_nil, rfl⟩
  | [i], _, c, h => by
    obtain ⟨o, ho, os, hos, rfl⟩ := isChoice_cons_iff.mp h
    rw [List.map_nil, isChoice_nil_iff] at hos
    subst hos
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    exact ⟨fun _ => a, fun j hj => by rw [List.mem_singleton] at hj; subst hj; exact ha, rfl⟩
  | i :: j :: l, hnd, c, h => by
    obtain ⟨o, ho, os, hos, rfl⟩ := isChoice_cons_iff.mp h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    have hnd' : (j :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hi : i ∉ j :: l := (List.nodup_cons.mp hnd).1
    obtain ⟨f, hf, rfl⟩ := isChoice_map_iff F A (j :: l) hnd' os hos
    refine ⟨fun k => if k = i then a else f k, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp only [if_true]
        exact ha
      · simp only [hki, if_false]
        rcases List.mem_cons.mp hk with hk | hk
        · exact absurd hk hki
        · exact hf k hk
    · show F i a :: List.map (fun i => F i (f i)) (j :: l) =
        F i (if i = i then a else f i) :: List.map (fun k => F k (if k = i then a else f k)) (j :: l)
      rw [if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hki : k ≠ i := fun he => hi (he ▸ hk)
      rw [if_neg hki]

theorem nodup_newTriples (k : Nat) : (newTriples k).Nodup := by
  unfold newTriples
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun b _ => ?_, ?_⟩
    · split
      · exact List.pairwise_singleton _ _
      · exact List.Pairwise.nil
    · refine List.Pairwise.imp_of_mem (fun {b b'} _ _ hbb' => ?_) List.nodup_range
      intro x hx y hy hxy
      split at hx <;> split at hy <;> simp_all
  · refine List.Pairwise.imp_of_mem (fun {a a'} _ _ haa' => ?_) List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_flatMap] at hx hy
    obtain ⟨b, _, hb⟩ := hx
    obtain ⟨b', _, hb'⟩ := hy
    split at hb <;> split at hb' <;> simp_all

/-- Choices for the pair groups of label `k`. -/
theorem isChoice_pairs (k : Nat) :
    ∀ (l : List Nat) (c : List (Opt (List Nat))), l.Nodup →
      IsChoice c (l.map (fun a => pairOptions a k)) →
        ∃ g : Nat → Option Bool, c = l.map (fun a => pairChoice a k (g a))
  | [], c, _, h => by
    rw [List.map_nil, isChoice_nil_iff] at h
    exact ⟨fun _ => none, h⟩
  | a :: l, c, hnd, h => by
    obtain ⟨o, ho, os, hos, rfl⟩ := isChoice_cons_iff.mp h
    obtain ⟨g, rfl⟩ := isChoice_pairs k l os (List.nodup_cons.mp hnd).2 hos
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have hoo : ∃ v : Option Bool, o = pairChoice a k v := by
      simp only [pairOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact ⟨none, rfl⟩
      · exact ⟨some true, rfl⟩
      · exact ⟨some false, rfl⟩
    obtain ⟨v, rfl⟩ := hoo
    refine ⟨fun b => if b = a then v else g b, ?_⟩
    simp only [List.map_cons, if_true, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro b hb
    have hba : b ≠ a := fun he => ha (he ▸ hb)
    simp only [hba, if_false]

/-- Choices for the groups introduced with label `k`. -/
theorem isChoice_groupsNew_iff (k : Nat) (c : List (Opt (List Nat)))
    (h : IsChoice c (groupsNew k)) :
    ∃ (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (g : Nat → Option Bool),
      (∀ t, t ∈ newTriples k → lawN t ∈ lawsExtreme) ∧
      c = (newTriples k).map (fun t => holdsL t.1 t.2.1 t.2.2 (lawN t)) ++
        (List.range k).map (fun a => pairChoice a k (g a)) := by
  obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := isChoice_append.mp h
  obtain ⟨f, hf, rfl⟩ := isChoice_map_iff (fun t => holdsL t.1 t.2.1 t.2.2) (fun _ => lawsExtreme)
    (newTriples k) (nodup_newTriples k) c₁ h₁
  obtain ⟨g, rfl⟩ := isChoice_pairs k (List.range k) c₂ List.nodup_range h₂
  exact ⟨f, g, hf, rfl⟩

/-- `choiceEPN` only reads laws on triples with largest label `< k` and pairs `(a, c)`, `c < k`. -/
theorem choiceEPN_congr {lawN lawN' : Nat × Nat × Nat → Fin 3 × Fin 3}
    {pairN pairN' : Nat → Nat → Option Bool} :
    ∀ k, (∀ j t, j < k → t ∈ newTriples j → lawN t = lawN' t) →
      (∀ a c, c < k → pairN a c = pairN' a c) →
      choiceEPN lawN pairN k = choiceEPN lawN' pairN' k
  | 0, _, _ => rfl
  | k + 1, hl, hp => by
    show choiceEPN lawN pairN k ++ choiceNew lawN pairN k =
      choiceEPN lawN' pairN' k ++ choiceNew lawN' pairN' k
    rw [choiceEPN_congr k (fun j t hj ht => hl j t (by omega) ht)
      (fun a c hc => hp a c (by omega))]
    congr 1
    unfold choiceNew
    congr 1
    · apply List.map_congr_left
      intro t ht
      rw [hl k t (by omega) ht]
    · apply List.map_congr_left
      intro a _
      rw [hp a k (by omega)]


/-- **Every choice for `groupsEP n` is `choiceEPN lawN pairN n`** for an extreme `lawN`. -/
theorem isChoice_groupsEP_iff :
    ∀ (n : Nat) (c : List (Opt (List Nat))), IsChoice c (groupsEP n) →
      ∃ (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool),
        (∀ t, lawN t ∈ lawsExtreme) ∧ c = choiceEPN lawN pairN n
  | 0, c, h => by
    rw [show groupsEP 0 = [] from rfl, isChoice_nil_iff] at h
    exact ⟨fun _ => (0, 0), fun _ _ => none, fun _ => mem_lawsExtreme (0, 0) (by decide), h⟩
  | k + 1, c, h => by
    obtain ⟨cOld, cNew, rfl, hOld, hNew⟩ := isChoice_groupsEP_succ.mp h
    obtain ⟨lawN, pairN, hlaw, rfl⟩ := isChoice_groupsEP_iff k cOld hOld
    obtain ⟨lawK, g, hlawK, rfl⟩ := isChoice_groupsNew_iff k cNew hNew
    -- merge: triples with largest label `k` and pairs `(a, k)` use the new data
    refine ⟨fun t => if t.2.2 = k then (if t ∈ newTriples k then lawK t else (0, 0)) else lawN t,
      fun a c => if c = k then g a else pairN a c, ?_, ?_⟩
    · intro t
      by_cases h1 : t.2.2 = k
      · show (if t.2.2 = k then (if t ∈ newTriples k then lawK t else (0, 0)) else lawN t) ∈ lawsExtreme
        rw [if_pos h1]
        by_cases h2 : t ∈ newTriples k
        · rw [if_pos h2]
          exact hlawK t h2
        · rw [if_neg h2]
          decide
      · show (if t.2.2 = k then (if t ∈ newTriples k then lawK t else (0, 0)) else lawN t) ∈ lawsExtreme
        rw [if_neg h1]
        exact hlaw t
    · show choiceEPN lawN pairN k ++ _ = choiceEPN _ _ k ++ choiceNew _ _ k
      congr 1
      · exact choiceEPN_congr k
          (fun j t hj ht => by
            have h3 := (mem_newTriples.mp ht).2.2
            exact (if_neg (show t.2.2 ≠ k by omega)).symm)
          (fun a c hc => (if_neg (show c ≠ k by omega)).symm)
      · unfold choiceNew
        congr 1
        · apply List.map_congr_left
          intro t ht
          have h3 := (mem_newTriples.mp ht).2.2
          dsimp only
          rw [if_pos h3, if_pos ht]
        · apply List.map_congr_left
          intro a _
          dsimp only
          rw [if_pos rfl]

end CDCert.K6
