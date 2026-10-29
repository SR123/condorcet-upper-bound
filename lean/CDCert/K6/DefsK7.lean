/-
CDCert.K6.DefsK7 — kernel-friendly evaluation of options on packed comparisons.

* `codeOf d`: an option packed into a natural number (kind, labels, law);
* `evalK code cm`: the option evaluated on packed comparisons with raw operations;
  `evalK_codeOf`: it is `evalD`;
* `maskOfK cms code`: the mask over a list of packed comparisons; `maskOfK_eq`: it is
  `maskOfN cms (evalD d)`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex7

namespace CDCert.K6

/-- Packed option: `0` no constraint, `1 + 4(a + 8b)` the pair `a` above `b`,
`2 + 4(a + 8(b + 8(c + 8(e + 4p))))` the law `(e, p)` on `(a, b, c)`. -/
def codeOf : OptD → Nat
  | .top => 0
  | .pr a b => 1 + 4 * (a + 8 * b)
  | .law a b c l => 2 + 4 * (a + 8 * (b + 8 * (c + 8 * (l.1.val + 4 * l.2.val))))

/-- Bit `i` of `cm`, with raw operations. -/
def bitK (cm i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight cm i) 1) 1

/-- Comparison `a` above `b` from packed comparisons. -/
noncomputable def cmpK (cm a b : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.not (bitK cm (Nat.add (Nat.mul 7 b) a)))
    (bitK cm (Nat.add (Nat.mul 7 a) b)) (Nat.blt a b)

/-- Never-condition from packed comparisons. -/
noncomputable def nvK (cm x y z p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (Bool.not (Bool.and (cmpK cm x y) (cmpK cm x z)))
    (fun q _ => Nat.rec (motive := fun _ => Bool) (Bool.not (Bool.xor (cmpK cm x y) (cmpK cm x z)))
      (fun _ _ => Bool.or (cmpK cm x y) (cmpK cm x z)) q) p

/-- Option evaluation from its code. -/
noncomputable def evalK (code cm : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k _ => Nat.rec (motive := fun _ => Bool)
      (cmpK cm (Nat.mod (Nat.div code 4) 8) (Nat.mod (Nat.div code 32) 8))
      (fun _ _ =>
        Nat.rec (motive := fun _ => Bool)
          (nvK cm (Nat.mod (Nat.div code 4) 8) (Nat.mod (Nat.div code 32) 8) (Nat.mod (Nat.div code 256) 8)
            (Nat.mod (Nat.div code 8192) 4))
          (fun e _ => Nat.rec (motive := fun _ => Bool)
            (nvK cm (Nat.mod (Nat.div code 32) 8) (Nat.mod (Nat.div code 4) 8) (Nat.mod (Nat.div code 256) 8)
              (Nat.mod (Nat.div code 8192) 4))
            (fun _ _ => nvK cm (Nat.mod (Nat.div code 256) 8) (Nat.mod (Nat.div code 4) 8)
              (Nat.mod (Nat.div code 32) 8) (Nat.mod (Nat.div code 8192) 4)) e)
          (Nat.mod (Nat.div code 2048) 4)) k)
    (Nat.mod code 4)

/-- Mask over a list of packed comparisons, with raw recursion. -/
noncomputable def maskOfK (cms : List Nat) (code : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add (Nat.mul 2 ih) (cond (evalK code x) 1 0)) cms

theorem bitK_eq (cm i : Nat) : bitK cm i = cm.testBit i := by
  unfold bitK
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  have h : Nat.land (Nat.shiftRight cm i) 1 = (cm >>> i) % 2 := Nat.and_one_is_mod _
  rw [h]
  have h2 : (cm >>> i) % 2 < 2 := Nat.mod_lt _ (by omega)
  generalize (cm >>> i) % 2 = r at h2 ⊢
  match r, h2 with
  | 0, _ => rfl
  | 1, _ => rfl

theorem cmpK_eq (cm a b : Nat) : cmpK cm a b = cmpB cm a b := by
  unfold cmpK cmpB
  cases h : Nat.blt a b
  · have : ¬ a < b := fun hab => by rw [Nat.blt_eq.mpr hab] at h; cases h
    simp only [if_neg this, bitK_eq]
    show (!(cm.testBit (7 * b + a))) = _
    rfl
  · have : a < b := Nat.blt_eq.mp h
    simp only [if_pos this, bitK_eq]
    rfl

theorem nvK_eq (cm x y z : Nat) (p : Fin 3) : nvK cm x y z p.val = nvB cm x y z p := by
  obtain ⟨p, hp⟩ := p
  unfold nvK nvB
  simp only [cmpK_eq]
  have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rfl
  · show (!(Bool.xor (cmpB cm x y) (cmpB cm x z))) = _
    cases cmpB cm x y <;> cases cmpB cm x z <;> rfl
  · rfl

theorem evalK_codeOf {d : OptD} (hd : d.WF) (cm : Nat) : evalK (codeOf d) cm = evalD d cm := by
  cases d with
  | top => rfl
  | pr a b =>
    obtain ⟨ha, hb, _⟩ := hd
    have h1 : Nat.mod (codeOf (.pr a b)) 4 = 1 := by show (1 + 4 * (a + 8 * b)) % 4 = 1; omega
    have h2 : Nat.mod (Nat.div (codeOf (.pr a b)) 4) 8 = a := by
      show (1 + 4 * (a + 8 * b)) / 4 % 8 = a; omega
    have h3 : Nat.mod (Nat.div (codeOf (.pr a b)) 32) 8 = b := by
      show (1 + 4 * (a + 8 * b)) / 32 % 8 = b; omega
    unfold evalK
    rw [h1, h2, h3, cmpK_eq]
    rfl
  | law a b c l =>
    obtain ⟨h1, h2, h3⟩ := hd
    obtain ⟨⟨e, he⟩, ⟨p, hp⟩⟩ := l
    have k0 : Nat.mod (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 4 = 2 := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) % 4 = 2; omega
    have ka : Nat.mod (Nat.div (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 4) 8 = a := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) / 4 % 8 = a; omega
    have kb : Nat.mod (Nat.div (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 32) 8 = b := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) / 32 % 8 = b; omega
    have kc : Nat.mod (Nat.div (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 256) 8 = c := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) / 256 % 8 = c; omega
    have ke : Nat.mod (Nat.div (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 2048) 4 = e := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) / 2048 % 4 = e; omega
    have kp : Nat.mod (Nat.div (codeOf (.law a b c (⟨e, he⟩, ⟨p, hp⟩))) 8192) 4 = p := by
      show (2 + 4 * (a + 8 * (b + 8 * (c + 8 * (e + 4 * p))))) / 8192 % 4 = p; omega
    unfold evalK
    rw [k0, ka, kb, kc, ke, kp]
    have hp' : nvK cm a b c p = nvB cm a b c ⟨p, hp⟩ := nvK_eq cm a b c ⟨p, hp⟩
    have hp1 : nvK cm b a c p = nvB cm b a c ⟨p, hp⟩ := nvK_eq cm b a c ⟨p, hp⟩
    have hp2 : nvK cm c a b p = nvB cm c a b ⟨p, hp⟩ := nvK_eq cm c a b ⟨p, hp⟩
    have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases this with rfl | rfl | rfl
    · show nvK cm a b c p = evalD (.law a b c (⟨0, he⟩, ⟨p, hp⟩)) cm
      rw [hp']; rfl
    · show nvK cm b a c p = evalD (.law a b c (⟨1, he⟩, ⟨p, hp⟩)) cm
      rw [hp1]; rfl
    · show nvK cm c a b p = evalD (.law a b c (⟨2, he⟩, ⟨p, hp⟩)) cm
      rw [hp2]; rfl

theorem maskOfK_eq {d : OptD} (hd : d.WF) : ∀ (cms : List Nat), maskOfK cms (codeOf d) = maskOfN cms (evalD d)
  | [] => rfl
  | x :: xs => by
    show Nat.add (Nat.mul 2 (maskOfK xs (codeOf d))) (cond (evalK (codeOf d) x) 1 0) = _
    rw [maskOfK_eq hd xs, evalK_codeOf hd]
    show 2 * maskOfN xs (evalD d) + cond (evalD d x) 1 0 = 2 * maskOfN xs (evalD d) + (if evalD d x then 1 else 0)
    cases evalD d x <;> rfl

end CDCert.K6
