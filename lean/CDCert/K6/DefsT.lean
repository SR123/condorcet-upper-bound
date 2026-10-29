/-
CDCert.K6.DefsT — kernel-evaluated checks of the five-table (`CDCert.K6.Table5`).

* `invarOK T rows r`: the value of `r` is nonzero and every relabelling row maps
  `r` to a key with the same value;
* `cardOf`, `a5Of`, `a53Of`: number of orders, of directed adjacent swaps, and of
  swaps at position 3 of a five-mask, from the swap rows `sw5`/`sw53`;
* `fieldsOK T potT sw sw3 k r`: the value of `r` has type field `k`, the card, `A5`
  and `A53` fields recomputed from `r`, and the offset contributions
  `vB + 2^60 = K c + c pot − (D/5) A5 − ηD (c + 4[k = 866]) + 2^60`,
  `vT + 2^60 = − c pot − (D/5) A53 − 4ηD [k = 41] + 2^60`, with
  `pot = potT.find k − 2^40`, written without subtraction.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs5

namespace CDCert.K6

/-- Relabelling invariance of the table value at `r`. -/
noncomputable def invarOK (T : KTree) (rows : List (List Nat)) (r : Nat) : Bool :=
  Bool.and (Bool.not (Nat.beq (T.find r) 0))
    (List.rec (motive := fun _ => Bool) true
      (fun row _ ih => Bool.and (Nat.beq (T.find (relabelI row r)) (T.find r)) ih) rows)

/-- Number of set bits of `r` below the length of `sw`. -/
noncomputable def cardOf (sw : List (List Nat)) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ _ ih q => Nat.add (cond (Nat.testBit r q) 1 0) (ih (Nat.succ q))) sw 0

/-- Number of set bits of `r` at the indices listed in `row`. -/
noncomputable def countIn (r : Nat) (row : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add (cond (Nat.testBit r t) 1 0) ih) row

/-- Directed adjacent swaps of the five-mask `r`. -/
noncomputable def a5Of (sw : List (List Nat)) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun row _ ih q => Nat.add (cond (Nat.testBit r q) (countIn r row) 0) (ih (Nat.succ q))) sw 0

/-- Swaps at position 3 of the five-mask `r`. -/
noncomputable def a53Of (sw3 : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun t _ ih q => Nat.add (cond (Nat.testBit r q) (cond (Nat.testBit r t) 1 0) 0) (ih (Nat.succ q)))
    sw3 0

/-- `D/5`. -/
def cD5 : Nat := nat_lit 1769223456
/-- `ηD = D/152`. -/
def cE : Nat := nat_lit 58198140
/-- `K = 12D/19`. -/
def cK : Nat := nat_lit 5587021440
/-- `2^40`. -/
def off40 : Nat := nat_lit 1099511627776

/-- Fields of the table value of the representative `r` of type `k`. -/
noncomputable def fieldsOK (T potT : KTree) (sw : List (List Nat)) (sw3 : List Nat) (k r : Nat) :
    Bool :=
  Bool.and (Nat.beq (Nat.shiftRight (T.find r) 154) k)
  (Bool.and (Nat.beq (Nat.mod (Nat.shiftRight (T.find r) 128) 256) (cardOf sw r))
  (Bool.and (Nat.beq (Nat.mod (Nat.shiftRight (T.find r) 136) 1024) (a5Of sw r))
  (Bool.and (Nat.beq (Nat.mod (Nat.shiftRight (T.find r) 146) 256) (a53Of sw3 r))
  (Bool.and (Nat.beq
      (Nat.add (Nat.add (Nat.add (Nat.mod (T.find r) 18446744073709551616)
        (Nat.mul cD5 (a5Of sw r)))
        (Nat.mul cE (Nat.add (cardOf sw r) (cond (Nat.beq k 866) 4 0))))
        (Nat.mul (cardOf sw r) off40))
      (Nat.add (Nat.add off60 (Nat.mul cK (cardOf sw r))) (Nat.mul (cardOf sw r) (potT.find k))))
    (Nat.beq
      (Nat.add (Nat.add (Nat.add (Nat.mod (Nat.shiftRight (T.find r) 64) 18446744073709551616)
        (Nat.mul (cardOf sw r) (potT.find k)))
        (Nat.mul cD5 (a53Of sw3 r)))
        (cond (Nat.beq k 41) (Nat.mul 4 cE) 0))
      (Nat.add off60 (Nat.mul (cardOf sw r) off40)))))))

end CDCert.K6
