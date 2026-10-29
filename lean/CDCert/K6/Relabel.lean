/-
CDCert.K6.Relabel — the class of `groupsEP n` domains is closed under
relabelling.

For a bijection `f` of `ℕ` with inverse `g`, preserving `{a | a < n}`, the
transformed data `lawT f g lawN`, `pairT g pairN` (independent of `n`) satisfy

  `allows (choiceEPN (lawT f g lawN) (pairT g pairN) n) M ↔ allows (choiceEPN lawN pairN n) (M.map g)`

for every order `M` of `0..n-1` (`allows_choiceEPN_relabel`). The proof writes a
law on a triple as a never-condition on the *set* of its labels (`nvL`), which is
invariant under reordering the triple and transported by relabelling.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.ChoiceN
import CDCert.K6.Perm

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-! ### Never-conditions on label sets -/

/-- `x` is not at position `p` among the labels `T` (containing `x`) in `L`:
the number of other labels of `T` above `x` is not `p`. -/
def nvL (T : List Nat) (x p : Nat) (L : List Nat) : Bool :=
  !(((T.erase x).filter (fun w => before w x L)).length == p)

theorem nvL_perm {T T' : List Nat} (h : T.Perm T') (x p : Nat) (L : List Nat) :
    nvL T x p L = nvL T' x p L := by
  unfold nvL
  rw [((h.erase x).filter _).length_eq]

theorem map_erase_inj {f : Nat → Nat} (hf : Function.Injective f) (x : Nat) :
    ∀ T : List Nat, (T.map f).erase (f x) = (T.erase x).map f
  | [] => rfl
  | y :: T => by
    rw [List.map_cons, List.erase_cons, List.erase_cons]
    by_cases h : y = x
    · subst h; simp
    · have h' : f y ≠ f x := fun e => h (hf e)
      have e1 : (f y == f x) = false := by rw [beq_eq_false_iff_ne]; exact h'
      have e2 : (y == x) = false := by rw [beq_eq_false_iff_ne]; exact h
      rw [e1, e2]
      simp only [Bool.false_eq_true, if_false, List.map_cons, map_erase_inj hf x T]

theorem nvL_map {f : Nat → Nat} (hf : Function.Injective f) (T : List Nat) (x p : Nat)
    (L : List Nat) : nvL (T.map f) (f x) p (L.map f) = nvL T x p L := by
  unfold nvL
  have h1 : (T.map f).erase (f x) = (T.erase x).map f := map_erase_inj hf x T
  rw [h1, List.filter_map, List.length_map]
  congr 3
  apply List.filter_congr
  intro w _
  simp only [Function.comp, before_map f hf]

section Never
variable {L : List Nat} (hnd : L.Nodup)

include hnd in
theorem before_eq_not {a b : Nat} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    before a b L = !before b a L := by
  rcases before_total ha hb hab with h | h
  · rw [h, before_asymm hnd h]; rfl
  · rw [h, before_asymm hnd h]; rfl

include hnd in
/-- `neverL` as a never-condition on the label set. -/
theorem neverL_eq_nvL {x y z : Nat} (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (p : Fin 3) :
    neverL x y z p L = nvL [x, y, z] x p.val L := by
  unfold nvL neverL
  have he : [x, y, z].erase x = [y, z] := by simp
  rw [he]
  have h1 := before_eq_not hnd hx hy hxy
  have h2 := before_eq_not hnd hx hz hxz
  obtain ⟨p, hp⟩ := p
  simp only [List.filter_cons, List.filter_nil]
  cases hyx : before y x L <;> cases hzx : before z x L <;> rw [hyx] at h1 <;> rw [hzx] at h2 <;>
    simp only [h1, h2] <;>
    (have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
     rcases this with rfl | rfl | rfl <;> rfl)

end Never

/-! ### Triples -/

/-- The entry of a triple at index `e`. -/
def pick3 (e : Fin 3) (t : Nat × Nat × Nat) : Nat :=
  if e = 0 then t.1 else if e = 1 then t.2.1 else t.2.2

/-- The index of `x` in a triple (`2` if it is neither of the first two). -/
def idx3T (x : Nat) (t : Nat × Nat × Nat) : Fin 3 :=
  if x = t.1 then 0 else if x = t.2.1 then 1 else 2

/-- A triple as a list. -/
def tl (t : Nat × Nat × Nat) : List Nat := [t.1, t.2.1, t.2.2]

/-- Sorting three labels. -/
def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a < b then (if b < c then (a, b, c) else if a < c then (a, c, b) else (c, a, b))
  else (if a < c then (b, a, c) else if b < c then (b, c, a) else (c, b, a))

theorem sort3_perm (a b c : Nat) : (tl (sort3 a b c)).Perm [a, b, c] := by
  unfold sort3 tl
  split
  · split
    · exact List.Perm.refl _
    · split
      · exact List.Perm.cons a (List.Perm.swap b c [])
      · exact (List.Perm.swap a c [b]).trans (List.Perm.cons a (List.Perm.swap b c []))
  · split
    · exact List.Perm.swap a b [c]
    · split
      · exact (List.Perm.cons b (List.Perm.swap a c [])).trans (List.Perm.swap a b [c])
      · exact (List.Perm.swap b c [a]).trans ((List.Perm.cons b (List.Perm.swap a c [])).trans
          (List.Perm.swap a b [c]))

theorem sort3_sorted {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (sort3 a b c).1 < (sort3 a b c).2.1 ∧ (sort3 a b c).2.1 < (sort3 a b c).2.2 := by
  unfold sort3
  split <;> split <;> (try split) <;> simp only <;> omega

theorem eq_of_perm_sorted {t t' : Nat × Nat × Nat} (h : (tl t).Perm (tl t'))
    (h1 : t.1 < t.2.1) (h2 : t.2.1 < t.2.2) (h1' : t'.1 < t'.2.1) (h2' : t'.2.1 < t'.2.2) :
    t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  simp only [tl] at h h1 h2 h1' h2'
  have m1 : a' ∈ [a, b, c] := h.symm.subset (by simp)
  have m2 : b' ∈ [a, b, c] := h.symm.subset (by simp)
  have m3 : c' ∈ [a, b, c] := h.symm.subset (by simp)
  have n1 : a ∈ [a', b', c'] := h.subset (by simp)
  have n3 : c ∈ [a', b', c'] := h.subset (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2 m3 n1 n3
  have ha : a = a' := by omega
  have hc : c = c' := by omega
  have hb : b = b' := by omega
  subst ha hb hc
  rfl

theorem mem_tl_pick3 (e : Fin 3) (t : Nat × Nat × Nat) : pick3 e t ∈ tl t := by
  obtain ⟨e, he⟩ := e
  unfold pick3 tl
  have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp

theorem fin3_cases (e : Fin 3) : e = 0 ∨ e = 1 ∨ e = 2 :=
  match e with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => Or.inr (Or.inr rfl)
  | ⟨n + 3, h⟩ => absurd h (by omega)

theorem pick3_0 (t : Nat × Nat × Nat) : pick3 0 t = t.1 := rfl
theorem pick3_1 (t : Nat × Nat × Nat) : pick3 1 t = t.2.1 := rfl
theorem pick3_2 (t : Nat × Nat × Nat) : pick3 2 t = t.2.2 := rfl

theorem pick3_idx3T {x : Nat} {t : Nat × Nat × Nat} (h : x ∈ tl t) : pick3 (idx3T x t) t = x := by
  simp only [tl, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold idx3T
  by_cases h1 : x = t.1
  · rw [if_pos h1, pick3_0, h1]
  · rw [if_neg h1]
    by_cases h2 : x = t.2.1
    · rw [if_pos h2, pick3_1, h2]
    · rw [if_neg h2, pick3_2]
      rcases h with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h.symm

theorem holdsL_e0 (a b c : Nat) (p : Fin 3) : holdsL a b c (0, p) = neverL a b c p := rfl
theorem holdsL_e1 (a b c : Nat) (p : Fin 3) : holdsL a b c (1, p) = neverL b a c p := rfl
theorem holdsL_e2 (a b c : Nat) (p : Fin 3) : holdsL a b c (2, p) = neverL c a b p := rfl

/-- `holdsL` on an increasing triple as a never-condition on its label set. -/
theorem holdsL_eq_nvL {L : List Nat} (hnd : L.Nodup) {t : Nat × Nat × Nat}
    (hm : ∀ x, x ∈ tl t → x ∈ L) (h1 : t.1 < t.2.1) (h2 : t.2.1 < t.2.2) (law : Fin 3 × Fin 3) :
    holdsL t.1 t.2.1 t.2.2 law L = nvL (tl t) (pick3 law.1 t) law.2.val L := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨e, p⟩ := law
  simp only [tl, List.mem_cons, List.not_mem_nil, or_false] at hm h1 h2
  have ha : a ∈ L := hm a (Or.inl rfl)
  have hb : b ∈ L := hm b (Or.inr (Or.inl rfl))
  have hc : c ∈ L := hm c (Or.inr (Or.inr rfl))
  rcases fin3_cases e with rfl | rfl | rfl
  · rw [holdsL_e0, pick3_0]
    exact neverL_eq_nvL hnd ha hb hc (by omega) (by omega) (by omega) p
  · rw [holdsL_e1, pick3_1]
    rw [neverL_eq_nvL hnd hb ha hc (by omega) (by omega) (by omega) p]
    exact nvL_perm (List.Perm.swap a b [c]) b p.val L
  · rw [holdsL_e2, pick3_2]
    rw [neverL_eq_nvL hnd hc ha hb (by omega) (by omega) (by omega) p]
    exact nvL_perm ((List.Perm.swap a c [b]).trans (List.Perm.cons a (List.Perm.swap b c []))) c p.val L

/-! ### Transformed laws and pairs -/

section Transform
variable (f g : Nat → Nat)

/-- The law on the increasing triple `t'` after relabelling by `f` (inverse `g`):
the law of the preimage triple, re-indexed. -/
def lawT (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (t' : Nat × Nat × Nat) : Fin 3 × Fin 3 :=
  (idx3T (f (pick3 (lawN (sort3 (g t'.1) (g t'.2.1) (g t'.2.2))).1 (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)))) t',
    (lawN (sort3 (g t'.1) (g t'.2.1) (g t'.2.2))).2)

/-- Reverse a fixed comparison. -/
def flipO : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

/-- The fixed comparison on the pair `(a', c')` after relabelling. -/
def pairT (pairN : Nat → Nat → Option Bool) (a' c' : Nat) : Option Bool :=
  if g a' < g c' then pairN (g a') (g c') else flipO (pairN (g c') (g a'))

variable {f g}
variable (hfg : ∀ a, f (g a) = a) (hgf : ∀ a, g (f a) = a)

include hgf in
theorem injective_of_left_inv : Function.Injective f := fun a b h => by
  have := congrArg g h
  rwa [hgf, hgf] at this

include hfg in
theorem injective_of_right_inv : Function.Injective g := fun a b h => by
  have := congrArg f h
  rwa [hfg, hfg] at this

include hfg hgf in
theorem map_mem_orders {n : Nat} (hn : ∀ a, a < n ↔ g a < n) {M : List Nat} (hM : M ∈ orders n) :
    M.map g ∈ orders n := by
  rw [mem_orders_iff]
  apply perm_of_nodup_of_mem_iff
    ((nodup_of_mem_orders hM).map g (fun a b hab e => hab (injective_of_right_inv hfg e)))
    List.nodup_range
  intro a
  rw [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hn b).mp ((mem_of_mem_orders hM b).mp hb)
  · intro ha
    refine ⟨f a, (mem_of_mem_orders hM _).mpr ?_, hgf a⟩
    rw [hn, hgf]
    exact ha

include hfg hgf in
/-- The transported law on one triple. -/
theorem holdsL_lawT {n : Nat} (hn : ∀ a, a < n ↔ g a < n) (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    {M : List Nat} (hM : M ∈ orders n) {t' : Nat × Nat × Nat} (ht' : t' ∈ triplesN n) :
    holdsL t'.1 t'.2.1 t'.2.2 (lawT f g lawN t') M =
      holdsL (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)).1 (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)).2.1
        (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)).2.2 (lawN (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)))
        (M.map g) := by
  obtain ⟨h1, h2, h3⟩ := mem_triplesN.mp ht'
  have hgi := injective_of_right_inv hfg
  have hfi := injective_of_left_inv hgf
  have hM' := map_mem_orders hfg hgf hn hM
  have hperm0 := sort3_perm (g t'.1) (g t'.2.1) (g t'.2.2)
  have hsort0 := sort3_sorted (a := g t'.1) (b := g t'.2.1) (c := g t'.2.2)
    (fun e => by have := hgi e; omega) (fun e => by have := hgi e; omega)
    (fun e => by have := hgi e; omega)
  show holdsL t'.1 t'.2.1 t'.2.2 (idx3T (f (pick3 (lawN (sort3 (g t'.1) (g t'.2.1) (g t'.2.2))).1
    (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)))) t', (lawN (sort3 (g t'.1) (g t'.2.1) (g t'.2.2))).2) M = _
  generalize sort3 (g t'.1) (g t'.2.1) (g t'.2.2) = t at hperm0 hsort0 ⊢
  have hperm : (tl t).Perm ((tl t').map g) := hperm0
  obtain ⟨s1, s2⟩ := hsort0
  have hmemM : ∀ x, x ∈ tl t' → x ∈ M := by
    intro x hx
    rw [mem_of_mem_orders hM]
    simp only [tl, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  have hmemM' : ∀ x, x ∈ tl t → x ∈ M.map g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (hperm.subset hx)
    exact List.mem_map_of_mem (hmemM y hy)
  rw [holdsL_eq_nvL (nodup_of_mem_orders hM') hmemM' s1 s2]
  rw [holdsL_eq_nvL (nodup_of_mem_orders hM) hmemM h1 h2]
  -- move the right side through `f`
  have hMfg : (M.map g).map f = M := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id M]
    apply List.map_congr_left
    intro a _
    exact hfg a
  rw [← nvL_map hfi (tl t) (pick3 (lawN t).1 t) (lawN t).2.val (M.map g), hMfg]
  have hperm' : ((tl t).map f).Perm (tl t') := by
    have := hperm.map f
    rw [List.map_map] at this
    have e : ∀ l : List Nat, l.map (f ∘ g) = l := fun l => by
      induction l with
      | nil => rfl
      | cons a l ih => rw [List.map_cons, ih]; simp [Function.comp, hfg]
    rw [e] at this
    exact this
  rw [nvL_perm hperm']
  have hmem : f (pick3 (lawN t).1 t) ∈ tl t' :=
    hperm'.subset (List.mem_map_of_mem (mem_tl_pick3 _ _))
  show nvL (tl t') (pick3 (idx3T (f (pick3 (lawN t).1 t)) t') t') (lawN t).2.val M = _
  rw [pick3_idx3T hmem]

include hfg hgf in
theorem sort3_sort3 {n : Nat} (hn : ∀ a, a < n ↔ g a < n) {t : Nat × Nat × Nat} (ht : t ∈ triplesN n) :
    sort3 (f t.1) (f t.2.1) (f t.2.2) ∈ triplesN n ∧
    sort3 (g (sort3 (f t.1) (f t.2.1) (f t.2.2)).1) (g (sort3 (f t.1) (f t.2.1) (f t.2.2)).2.1)
      (g (sort3 (f t.1) (f t.2.1) (f t.2.2)).2.2) = t := by
  obtain ⟨h1, h2, h3⟩ := mem_triplesN.mp ht
  have hfi := injective_of_left_inv hgf
  have hgi := injective_of_right_inv hfg
  have hfn : ∀ a, a < n ↔ f a < n := fun a => by rw [hn (f a), hgf]
  have hp0 := sort3_perm (f t.1) (f t.2.1) (f t.2.2)
  have hs0 := sort3_sorted (a := f t.1) (b := f t.2.1) (c := f t.2.2)
    (fun e => by have := hfi e; omega) (fun e => by have := hfi e; omega)
    (fun e => by have := hfi e; omega)
  generalize sort3 (f t.1) (f t.2.1) (f t.2.2) = t' at hp0 hs0 ⊢
  have hp : (tl t').Perm [f t.1, f t.2.1, f t.2.2] := hp0
  obtain ⟨s1, s2⟩ := hs0
  have hlt : t'.2.2 < n := by
    have : t'.2.2 ∈ [f t.1, f t.2.1, f t.2.2] := hp.subset (by simp [tl])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h <;> rw [h] <;> exact (hfn _).mp (by omega)
  refine ⟨mem_triplesN.mpr ⟨s1, s2, hlt⟩, ?_⟩
  apply eq_of_perm_sorted _ _ _ h1 h2
  · have hq : (tl (sort3 (g t'.1) (g t'.2.1) (g t'.2.2))).Perm ((tl t').map g) := sort3_perm _ _ _
    refine hq.trans ((hp.map g).trans ?_)
    simp only [List.map_cons, List.map_nil, hgf, tl]
    exact List.Perm.refl _
  · have hgd : g t'.1 ≠ g t'.2.1 ∧ g t'.1 ≠ g t'.2.2 ∧ g t'.2.1 ≠ g t'.2.2 :=
      ⟨fun e => by have := hgi e; omega, fun e => by have := hgi e; omega,
        fun e => by have := hgi e; omega⟩
    exact (sort3_sorted hgd.1 hgd.2.1 hgd.2.2).1
  · have hgd : g t'.1 ≠ g t'.2.1 ∧ g t'.1 ≠ g t'.2.2 ∧ g t'.2.1 ≠ g t'.2.2 :=
      ⟨fun e => by have := hgi e; omega, fun e => by have := hgi e; omega,
        fun e => by have := hgi e; omega⟩
    exact (sort3_sorted hgd.1 hgd.2.1 hgd.2.2).2

include hfg hgf in
theorem triples_lawT_iff {n : Nat} (hn : ∀ a, a < n ↔ g a < n) (lawN : Nat × Nat × Nat → Fin 3 × Fin 3)
    {M : List Nat} (hM : M ∈ orders n) :
    (∀ t', t' ∈ triplesN n → holdsL t'.1 t'.2.1 t'.2.2 (lawT f g lawN t') M = true) ↔
      (∀ t, t ∈ triplesN n → holdsL t.1 t.2.1 t.2.2 (lawN t) (M.map g) = true) := by
  constructor
  · intro h t ht
    obtain ⟨ht', heq⟩ := sort3_sort3 hfg hgf hn ht
    have := h _ ht'
    rw [holdsL_lawT hfg hgf hn lawN hM ht', heq] at this
    exact this
  · intro h t' ht'
    rw [holdsL_lawT hfg hgf hn lawN hM ht']
    apply h
    obtain ⟨h1, h2, h3⟩ := mem_triplesN.mp ht'
    have hgi := injective_of_right_inv hfg
    have hd : g t'.1 ≠ g t'.2.1 ∧ g t'.1 ≠ g t'.2.2 ∧ g t'.2.1 ≠ g t'.2.2 :=
      ⟨fun e => by have := hgi e; omega, fun e => by have := hgi e; omega,
        fun e => by have := hgi e; omega⟩
    obtain ⟨s1, s2⟩ := sort3_sorted hd.1 hd.2.1 hd.2.2
    refine mem_triplesN.mpr ⟨s1, s2, ?_⟩
    have : (sort3 (g t'.1) (g t'.2.1) (g t'.2.2)).2.2 ∈ [g t'.1, g t'.2.1, g t'.2.2] :=
      (sort3_perm _ _ _).subset (by simp [tl])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h <;> rw [h] <;> exact (hn _).mp (by omega)

include hfg in
theorem pairChoice_pairT (pairN : Nat → Nat → Option Bool) {a' c' : Nat} (hac : a' ≠ c') (M : List Nat) :
    pairChoice a' c' (pairT g pairN a' c') M =
      (if g a' < g c' then pairChoice (g a') (g c') (pairN (g a') (g c')) (M.map g)
       else pairChoice (g c') (g a') (pairN (g c') (g a')) (M.map g)) := by
  have hgi := injective_of_right_inv hfg
  unfold pairT
  split
  · cases pairN (g a') (g c') with
    | none => rfl
    | some b =>
      cases b
      · show before c' a' M = before (g c') (g a') (M.map g)
        rw [before_map g hgi]
      · show before a' c' M = before (g a') (g c') (M.map g)
        rw [before_map g hgi]
  · cases pairN (g c') (g a') with
    | none => rfl
    | some b =>
      cases b
      · show before a' c' M = before (g a') (g c') (M.map g)
        rw [before_map g hgi]
      · show before c' a' M = before (g c') (g a') (M.map g)
        rw [before_map g hgi]

include hfg hgf in
theorem pairs_pairT_iff {n : Nat} (hn : ∀ a, a < n ↔ g a < n) (pairN : Nat → Nat → Option Bool)
    (M : List Nat) :
    (∀ a' c', a' < c' → c' < n → pairChoice a' c' (pairT g pairN a' c') M = true) ↔
      (∀ a c, a < c → c < n → pairChoice a c (pairN a c) (M.map g) = true) := by
  have hgi := injective_of_right_inv hfg
  have hfi := injective_of_left_inv hgf
  have hfn : ∀ a, a < n ↔ f a < n := fun a => by rw [hn (f a), hgf]
  constructor
  · intro h a c hac hc
    have hfa : f a ≠ f c := fun e => by have := hfi e; omega
    rcases Nat.lt_or_gt_of_ne hfa with hlt | hlt
    · have := h (f a) (f c) hlt ((hfn c).mp hc)
      rw [pairChoice_pairT hfg pairN (by omega), hgf, hgf, if_pos hac] at this
      exact this
    · have := h (f c) (f a) hlt ((hfn a).mp (by omega))
      rw [pairChoice_pairT hfg pairN (by omega), hgf, hgf, if_neg (by omega)] at this
      exact this
  · intro h a' c' hac hc
    rw [pairChoice_pairT hfg pairN (by omega)]
    have hgd : g a' ≠ g c' := fun e => by have := hgi e; omega
    have ha' : g a' < n := (hn a').mp (by omega)
    have hc' : g c' < n := (hn c').mp hc
    split
    · exact h _ _ (by assumption) hc'
    · exact h _ _ (by omega) ha'

include hfg hgf in
/-- **Relabelling a `choiceEPN` domain.** -/
theorem allows_choiceEPN_relabel {n : Nat} (hn : ∀ a, a < n ↔ g a < n)
    (lawN : Nat × Nat × Nat → Fin 3 × Fin 3) (pairN : Nat → Nat → Option Bool)
    {M : List Nat} (hM : M ∈ orders n) :
    allows (choiceEPN (lawT f g lawN) (pairT g pairN) n) M =
      allows (choiceEPN lawN pairN n) (M.map g) := by
  apply Bool.eq_iff_iff.mpr
  rw [allows_choiceEPN, allows_choiceEPN, triples_lawT_iff hfg hgf hn lawN hM,
    pairs_pairT_iff hfg hgf hn pairN M]

end Transform

theorem lawT_extreme {f g : Nat → Nat} {lawN : Nat × Nat × Nat → Fin 3 × Fin 3}
    (h : ∀ t, lawN t ∈ lawsExtreme) (t : Nat × Nat × Nat) : lawT f g lawN t ∈ lawsExtreme :=
  mem_lawsExtreme _ (ne_one_of_mem_lawsExtreme (lawN (sort3 (g t.1) (g t.2.1) (g t.2.2))) (h _))

end CDCert.K6
