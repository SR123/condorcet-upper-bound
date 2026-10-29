/-
CDCert.K6.Defs — kernel-evaluated definitions for the six-level finite check.

Everything here is a plain total function on natural numbers; the kernel
evaluates it by `decide +kernel` (no `native_decide`). Definitions are written
with raw recursors (`List.rec`, `Nat.casesOn`, `KTree.rec`) and raw `Nat`
operations, which the kernel reduces fastest. They are `noncomputable` only
because the code generator does not compile recursors; this does not affect
kernel reduction or logical content.

* `KTree` / `KTree.find`: binary search tree with natural keys and values
  (`0` for a missing key).
* `dfs2 leafOK gs b t`: depth-first check over a list of groups of option pairs
  `(bottom-indexed mask, top-indexed mask)`: every option is intersected with
  the current pair of masks; an empty intersection is skipped; at the end
  `leafOK` is applied. New states are forced to the canonical form
  `Nat.succ (lit k)` by `Nat.casesOn`, so the kernel's whnf cache memoizes
  repeated (level, state) pairs. The soundness theorem (`dfs2_sound`, in
  `CDCert.K6.Sound`) is independent of this operational remark.
* `sliceVal`, `leafOK6`: the six-level leaf test. A six-domain is given by its
  masks `b` over the bottom-indexed base (index `120*x + i`, order
  `L_i.map (up x) ++ [x]`) and `t` over the top-indexed base (index `120*y + i`,
  order `y :: L_i.map (up y)`), where `L_i` is the `i`-th five-order in
  lexicographic order; so its bottom and top five-slices are the 120-bit
  blocks. Each nonempty slice is looked up in the five-table; a missing slice
  makes the test fail.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Tree


namespace CDCert.K6

/-- `all` over a list of natural numbers, with the recursor. -/
noncomputable def allNat (p : Nat → Bool) (g : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun o _ ih => Bool.and (p o) ih) g

/-- A 62-bit prime (`2^62 - 57`) used only to spread kernel cache keys. -/
def hashP : Nat := nat_lit 4611686018427387847

/-- Cache-friendly encoding: `x` in the high bits, `x % hashP` in the low 64 bits.
(The kernel hashes natural-number literals by their low bits; masks with equal
low bits would otherwise collide in its whnf cache.) -/
def enc (x : Nat) : Nat := Nat.lor (Nat.shiftLeft x 64) (Nat.mod x hashP)

/-- Inverse of `enc` on its image. -/
def dec (e : Nat) : Nat := Nat.shiftRight e 64

/-- One DFS step in encoded form. States are `e = s * 2^64 + h` with `h < 2^64`;
options are pre-shifted masks `o * 2^64`; the new state is
`x + x % hashP` with `x = e &&& (o * 2^64) = (s &&& o) * 2^64`. Written inline, with
raw operations, so that the kernel caches as few intermediate terms as possible. -/
def stepEnc (e o : Nat) : Nat := Nat.lor (Nat.land e o) (Nat.mod (Nat.land e o) hashP)

/-- Memoizing depth-first check over groups of pre-shifted options (see `stepEnc`).
Empty intersections are skipped; at the end `leafOK` is applied to the encoded state.
Written with `List.rec`, `Bool.rec` and `Nat.rec` only (`Bool.rec false r b` is
`b && r`; `Nat.rec true (fun e' _ => k (e'+1)) x` is the case split on `x = 0`). -/
noncomputable def dfs1 (leafOK : Nat → Bool) (gs : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) leafOK
    (fun g _ ih e => List.rec (motive := fun _ => Bool) true
      (fun o _ r => Bool.rec (motive := fun _ => Bool) false r
        (Nat.rec (motive := fun _ => Bool) true (fun e' _ => ih (Nat.succ e')) (stepEnc e o))) g) gs

/-! ### Linear five-slice contributions

A table value packs `(vB + 2^60) + 2^64 (vT + 2^60) + 2^128 card + 2^136 A5 +
2^146 A53 + 2^154 type` (the last four fields are used only in proofs), where, with
`D = 8846117280`, `K = 12 D / 19`, `D/5`, `η D = D/152`,
* `vB(L) = K |L| + |L| pot(L) - (D/5) A5(L) - η D (|L| + 4 [type L = 866])`,
* `vT(L) = - |L| pot(L) - (D/5) A53(L) - 4 η D [type L = 41]`,
`A5` counting directed adjacent swaps of `L` and `A53` those at its last position.
For a six-domain `H` the six-row inequality `D s(H) ≥ η D (|H| + 4 rb + 4 rt)` is
exactly `Σ_bottom vB + Σ_top vT ≥ 0`. -/

/-- `2^60`, the offset of the stored contributions. -/
def off60 : Nat := nat_lit 1152921504606846976

/-- `2^64 - 1`. -/
def m64 : Nat := nat_lit 18446744073709551615

/-- `2^120 - 1`. -/
def m120 : Nat := nat_lit 1329227995784915872903807060280344575

/-- Offset bottom contribution at the encoded key `s` (key `s / 2^64`); `0` if absent. -/
noncomputable def lookB (T : KTree) (s : Nat) : Nat :=
  Nat.land (T.find (Nat.shiftRight s 64)) m64

/-- Offset top contribution at the encoded key `s`; `0` if absent. -/
noncomputable def lookT (T : KTree) (s : Nat) : Nat :=
  Nat.land (Nat.shiftRight (T.find (Nat.shiftRight s 64)) 64) m64

/-- Offset bottom contribution of the 120-bit block at bit offset `k` of `m`:
`2^60` (neutral) if the block is empty, the memoized table contribution otherwise
(`0`, which makes the test fail, if a nonempty block is not a key). -/
noncomputable def blkB (T : KTree) (m k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) off60 (fun s' _ => lookB T (Nat.succ s'))
    (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight m k) m120) 64)
      (Nat.mod (Nat.land (Nat.shiftRight m k) m120) hashP))

/-- Offset top contribution of the 120-bit block at bit offset `k` of `m`. -/
noncomputable def blkT (T : KTree) (m k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) off60 (fun s' _ => lookT T (Nat.succ s'))
    (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight m k) m120) 64)
      (Nat.mod (Nat.land (Nat.shiftRight m k) m120) hashP))

/-- `12 * 2^60`. -/
def off60x12 : Nat := nat_lit 13835058055282163712

/-- The six-row inequality for the combined mask `m` (bottom-indexed in bits
`0..719`, top-indexed in bits `720..1439`): the sum of the twelve offset
contributions is at least `12 * 2^60`. -/
noncomputable def ineq6 (T : KTree) (m : Nat) : Bool :=
  Nat.ble off60x12
    (Nat.add (blkB T m 0) (Nat.add (blkB T m 120) (Nat.add (blkB T m 240)
    (Nat.add (blkB T m 360) (Nat.add (blkB T m 480) (Nat.add (blkB T m 600)
    (Nat.add (blkT T m 720) (Nat.add (blkT T m 840) (Nat.add (blkT T m 960)
    (Nat.add (blkT T m 1080) (Nat.add (blkT T m 1200) (blkT T m 1320))))))))))))

/-- `2^720 - 1`. -/
def m720 : Nat := Nat.sub (Nat.shiftLeft 1 720) 1

/-- The six-level leaf test on the encoded combined state: the six-row inequality
holds, or the bottom-indexed mask is one of the listed exceptional labelled domains. -/
noncomputable def leafOK6 (T E : KTree) (e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.not (Nat.beq (E.find (Nat.land (Nat.shiftRight e 64) m720)) 0)) true
    (ineq6 T (Nat.shiftRight e 64))

/-- OR of the lifted combined masks of the five-orders present in the five-mask
`r` (`lifts` lists, for each five-order index in order, its lifted mask). -/
noncomputable def liftOf (lifts : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun o _ ih q acc => cond (Nat.testBit r q) (ih (Nat.succ q) (Nat.lor acc o)) (ih (Nat.succ q) acc))
    lifts 0 0

end CDCert.K6
