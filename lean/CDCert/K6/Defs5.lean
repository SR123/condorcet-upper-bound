/-
CDCert.K6.Defs5 — kernel-evaluated definitions for relabelling witnesses
(five-level coverage via the four-type tower, table invariance, exceptional
witnesses).

* `rlab σ L`: relabel the order `L` by the permutation `σ` (a list: label `a`
  becomes `σ[a]`; labels outside `σ` are kept).
* `lexIdx L`: the Lehmer-code index of `L`; on `lexOrders n` it is the position
  (checked by the kernel where used).
* `relabelI row d`: the mask with bit `row[q]` for every bit `q` of `d` — the image
  of the domain with mask `d` when `row[q]` is the index of the image of the
  `q`-th order.
* `getL rows s`: the `s`-th row.
* `leafW rows nperm nrep hint repT e`: witness leaf test. The hint value `h` of
  the decoded state `d` is `1 + t + 256 * k`; the test checks `t < nperm`,
  `k < nrep` and `relabelI rows[t] d = repT.find k`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs

namespace CDCert.K6

/-- Relabel an order: label `a` becomes `σ.getD a a`. -/
def rlab (σ : List Nat) (L : List Nat) : List Nat := L.map (fun a => σ.getD a a)

/-- Factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Lehmer-code index of a list (lexicographic rank among the permutations of its
entries when they are `0..n-1`). -/
def lexIdx : List Nat → Nat
  | [] => 0
  | a :: rest => rest.countP (fun b => decide (b < a)) * fact rest.length + lexIdx rest

/-- The image mask: bit `row[q]` for every set bit `q` of `d`. -/
noncomputable def relabelI (row : List Nat) (d : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun t _ ih q acc => cond (Nat.testBit d q) (ih (Nat.succ q) (Nat.lor acc (Nat.shiftLeft 1 t)))
      (ih (Nat.succ q) acc))
    row 0 0

/-- The `s`-th row (`[]` beyond the end). -/
noncomputable def getL (rows : List (List Nat)) (s : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun r _ ih j => Nat.rec (motive := fun _ => List Nat) r (fun j' _ => ih j') j) rows s

/-- Witness leaf test on the encoded state `e` (decoded mask `e >>> 64`): the hint
`1 + t + 256 k` has `t < nperm`, `k < nrep`, and row `t` maps the mask to `repT.find k`. -/
noncomputable def leafW (rows : List (List Nat)) (nperm nrep : Nat) (hint repT : KTree) (e : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun h _ => Bool.and (Nat.blt (Nat.mod h 256) nperm) (Bool.and (Nat.blt (Nat.div h 256) nrep)
      (Nat.beq (relabelI (getL rows (Nat.mod h 256)) (Nat.shiftRight e 64))
        (repT.find (Nat.div h 256)))))
    (hint.find (Nat.shiftRight e 64))

/-- All values of a tree satisfy `p`. -/
noncomputable def KTree.allVals (p : Nat → Bool) (t : KTree) : Bool :=
  KTree.rec (motive := fun _ => Bool) true (fun _ _ v _ ihl ihr => Bool.and (p v) (Bool.and ihl ihr)) t

end CDCert.K6
