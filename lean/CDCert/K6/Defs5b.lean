/-
CDCert.K6.Defs5b — kernel-friendly variants of `relabelI` and `leafW` (`CDCert.K6.Defs5`):
bits are tested by `bitQ d q = Nat.beq (Nat.land (Nat.shiftRight d q) 1) 1`, which the kernel
evaluates with its built-in arithmetic (`Nat.testBit` goes through `Nat.decEq` and costs about
16 KB of kernel terms per call). They agree with the originals (`relabelIq_eq`, `leafWq_eq`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs5

namespace CDCert.K6

/-- Bit `q` of `d`, with the kernel's built-in operations. -/
def bitQ (d q : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight d q) 1) 1

/-- `relabelI` with the kernel-friendly bit test. -/
noncomputable def relabelIq (row : List Nat) (d : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun t _ ih q acc => cond (bitQ d q) (ih (Nat.succ q) (Nat.lor acc (Nat.shiftLeft 1 t)))
      (ih (Nat.succ q) acc))
    row 0 0

/-- `leafW` through `relabelIq`. -/
noncomputable def leafWq (rows : List (List Nat)) (nperm nrep : Nat) (hint repT : KTree) (e : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun h _ => Bool.and (Nat.blt (Nat.mod h 256) nperm) (Bool.and (Nat.blt (Nat.div h 256) nrep)
      (Nat.beq (relabelIq (getL rows (Nat.mod h 256)) (Nat.shiftRight e 64))
        (repT.find (Nat.div h 256)))))
    (hint.find (Nat.shiftRight e 64))

theorem bitQ_eq (d q : Nat) : bitQ d q = d.testBit q := by
  unfold bitQ
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  have h : Nat.land (Nat.shiftRight d q) 1 = (d >>> q) % 2 := Nat.and_one_is_mod _
  rw [h]
  have h2 : (d >>> q) % 2 < 2 := Nat.mod_lt _ (by omega)
  generalize (d >>> q) % 2 = r at h2 ⊢
  match r, h2 with
  | 0, _ => rfl
  | 1, _ => rfl

theorem relabelIq_aux (d : Nat) : ∀ (row : List Nat) (q acc : Nat),
    (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun t _ ih q acc => cond (bitQ d q) (ih (Nat.succ q) (Nat.lor acc (Nat.shiftLeft 1 t)))
        (ih (Nat.succ q) acc)) row) q acc =
    (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun t _ ih q acc => cond (Nat.testBit d q) (ih (Nat.succ q) (Nat.lor acc (Nat.shiftLeft 1 t)))
        (ih (Nat.succ q) acc)) row) q acc
  | [], _, _ => rfl
  | t :: row, q, acc => by
    show cond (bitQ d q) _ _ = cond (Nat.testBit d q) _ _
    rw [bitQ_eq, relabelIq_aux d row (Nat.succ q), relabelIq_aux d row (Nat.succ q)]

theorem relabelIq_eq : relabelIq = relabelI := by
  funext row d
  exact relabelIq_aux d row 0 0

theorem leafWq_eq : leafWq = leafW := by
  funext rows nperm nrep hint repT e
  unfold leafWq leafW
  rw [relabelIq_eq]

end CDCert.K6
