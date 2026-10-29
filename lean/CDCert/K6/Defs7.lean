/-
CDCert.K6.Defs7 — kernel-evaluated definitions for the seven-level seed checks.

A seven-domain `J` is a 15120-bit mask over `base7` (three copies of the orders of
`0..6`, see `CDCert.K6.Lex7`): copy 1 lists, for each last label `z`, the bottom
six-slice `B_z J` in the bottom-indexed base `baseB 5`; copy 2 lists, for each first
label `w`, the top six-slice `T_w J` in `baseT 5`; copy 3 lists `T_w J` in `baseB 5`.
So every five-slice of every six-slice is a 120-bit block at a fixed offset.

* `dfsP`: memoized DFS (as `dfs1`) with a prune mask per level: a state meeting the
  level's prune mask is skipped (no exact completion exists);
* `cB`, `cT`, `cCard`, `cA5`, `cA53`, `c866`, `c41`: table fields of a five-block
  (neutral values for the empty block), looked up through the cache-friendly `enc`;
* a six-slice is described by the offsets `oB` of its bottom five-blocks, `oT` of its
  top five-blocks and `oH` of its bottom-indexed 720-bit mask; `sDs` is
  `D s + 12·2^60` for it, `sKey` its invariant key, `sP` its `2Dp + 2^62`, `sOK` that
  its S-status is certified (hinted, or its key is not an S key);
* `leaf7`: if the seed slice at offset `oSeed` is exactly `seed`, all slices are
  certified and `Σ_bottom (2D θ_b) + Σ_top (2D θ_t) ≥ 2ηD |J|` (with offsets).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.DefsT

namespace CDCert.K6

/-- Memoizing DFS with a prune mask per level (`gs` pairs a group with the prune mask
applied to the states it produces). -/
noncomputable def dfsP (leafOK : Nat → Bool) (gs : List (List Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) leafOK
    (fun g _ ih e => List.rec (motive := fun _ => Bool) true
      (fun o _ r => Bool.rec (motive := fun _ => Bool) false r
        (Nat.rec (motive := fun _ => Bool) true
          (fun e' _ => Bool.rec (motive := fun _ => Bool) true (ih (Nat.succ e'))
            (Nat.beq (Nat.land (Nat.succ e') g.2) 0))
          (stepEnc e o))) g.1) gs

/-- The 120-bit block at offset `o`. -/
def blk120 (m o : Nat) : Nat := Nat.land (Nat.shiftRight m o) m120

/-- Table value of a block given its encoding (`0` for the empty block). -/
noncomputable def tvE (T : KTree) (s : Nat) : Nat := T.find (Nat.shiftRight s 64)

/-- Offset bottom contribution `vB + 2^60` (`2^60` for the empty block). -/
noncomputable def cB (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) off60 (fun s _ => Nat.land (tvE T (Nat.succ s)) m64) (enc b)

/-- Offset top contribution `vT + 2^60` (`2^60` for the empty block). -/
noncomputable def cT (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) off60
    (fun s _ => Nat.land (Nat.shiftRight (tvE T (Nat.succ s)) 64) m64) (enc b)

/-- Card field (`0` for the empty block). -/
noncomputable def cCard (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s _ => Nat.mod (Nat.shiftRight (tvE T (Nat.succ s)) 128) 256) (enc b)

/-- `A5` field. -/
noncomputable def cA5 (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s _ => Nat.mod (Nat.shiftRight (tvE T (Nat.succ s)) 136) 1024) (enc b)

/-- `A53` field. -/
noncomputable def cA53 (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s _ => Nat.mod (Nat.shiftRight (tvE T (Nat.succ s)) 146) 256) (enc b)

/-- `1` if the block has type 866. -/
noncomputable def c866 (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun s _ => cond (Nat.beq (Nat.shiftRight (tvE T (Nat.succ s)) 154) 866) 1 0) (enc b)

/-- `1` if the block has type 41. -/
noncomputable def c41 (T : KTree) (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun s _ => cond (Nat.beq (Nat.shiftRight (tvE T (Nat.succ s)) 154) 41) 1 0) (enc b)

/-- Sum of `f (block at o)` over the offsets `os`. -/
noncomputable def sumOff (f : Nat → Nat) (m : Nat) (os : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun o _ ih => Nat.add (f (blk120 m o)) ih) os

/-- `D s(H) + 12·2^60` of a six-slice. -/
noncomputable def sDs (T : KTree) (m : Nat) (oB oT : List Nat) : Nat :=
  Nat.add (Nat.add (sumOff (cB T) m oB) (sumOff (cT T) m oT))
    (Nat.mul cE (Nat.add (sumOff (cCard T) m oB)
      (Nat.mul 4 (Nat.add (sumOff (c866 T) m oB) (sumOff (c41 T) m oT)))))

/-- Invariant key of a six-slice. -/
noncomputable def sKey (T : KTree) (m : Nat) (oB oT : List Nat) : Nat :=
  Nat.add (sumOff (cB T) m oB) (Nat.add (Nat.shiftLeft (sumOff (cT T) m oT) 70)
  (Nat.add (Nat.shiftLeft (sumOff (cCard T) m oB) 140) (Nat.add (Nat.shiftLeft (sumOff (c866 T) m oB) 150)
  (Nat.add (Nat.shiftLeft (sumOff (c41 T) m oT) 155) (Nat.add (Nat.shiftLeft (sumOff (cA5 T) m oB) 160)
    (Nat.shiftLeft (sumOff (cA53 T) m oT) 175))))))

/-- `2^720 - 1`. -/
def m720' : Nat := Nat.sub (Nat.shiftLeft 1 720) 1

/-- The bottom-indexed 720-bit mask of a six-slice. -/
def blk720 (m o : Nat) : Nat := Nat.land (Nat.shiftRight m o) m720'

/-- `2^62`. -/
def off62 : Nat := nat_lit 4611686018427387904

/-- `2D p(H) + 2^62`: from the S hint, or `4ηD (r_t − r_b) + 2^62`. -/
noncomputable def sP (T hintS psiT : KTree) (m : Nat) (oB oT : List Nat) (oH : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.sub (Nat.add (Nat.mul (Nat.mul 4 cE) (sumOff (c41 T) m oT)) off62)
      (Nat.mul (Nat.mul 4 cE) (sumOff (c866 T) m oB)))
    (fun h _ => psiT.find h) (hintS.find (blk720 m oH))

/-- The S-status of a six-slice is certified: it is hinted, or its key is not an S key. -/
noncomputable def sOK (T hintS sKeyT : KTree) (m : Nat) (oB oT : List Nat) (oH : Nat) : Bool :=
  Bool.or (Bool.not (Nat.beq (hintS.find (blk720 m oH)) 0)) (Nat.beq (sKeyT.find (sKey T m oB oT)) 0)

/-- A six-slice: offsets of its bottom five-blocks, top five-blocks, bottom-indexed mask. -/
abbrev Slc := List Nat × List Nat × Nat

/-- All slices certified. -/
noncomputable def allOK (T hintS sKeyT : KTree) (m : Nat) (ss : List Slc) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun s _ ih => Bool.and (sOK T hintS sKeyT m s.1 s.2.1 s.2.2) ih) ss

/-- `Σ (D s + 12·2^60 + 2D p + 2^62)` over bottom slices. -/
noncomputable def sumBot (T hintS psiT : KTree) (m : Nat) (ss : List Slc) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s _ ih => Nat.add (Nat.add (sDs T m s.1 s.2.1) (sP T hintS psiT m s.1 s.2.1 s.2.2)) ih) ss

/-- `2^63`. -/
def off63 : Nat := nat_lit 9223372036854775808

/-- `Σ (D s + 12·2^60 + 2^63 − (2D p + 2^62))` over top slices. -/
noncomputable def sumTop (T hintS psiT : KTree) (m : Nat) (ss : List Slc) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s _ ih => Nat.add (Nat.add (sDs T m s.1 s.2.1) (Nat.sub off63 (sP T hintS psiT m s.1 s.2.1 s.2.2))) ih) ss

/-- `|J|`: the cards of the bottom slices. -/
noncomputable def cardJ (T : KTree) (m : Nat) (ss : List Slc) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun s _ ih => Nat.add (sumOff (cCard T) m s.1) ih) ss

/-- `224 · 2^60`. -/
def off224 : Nat := nat_lit 258254417031933722624

/-- The seven-level leaf test. -/
noncomputable def leaf7 (T hintS psiT sKeyT : KTree) (bots tops : List Slc) (oSeed seed : Nat) (e : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.and (allOK T hintS sKeyT (Nat.shiftRight e 64) (bots ++ tops))
      (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 cE) (cardJ T (Nat.shiftRight e 64) bots)) off224)
        (Nat.add (sumBot T hintS psiT (Nat.shiftRight e 64) bots) (sumTop T hintS psiT (Nat.shiftRight e 64) tops))))
    (Nat.beq (blk720 (Nat.shiftRight e 64) oSeed) seed)

/-- Encoding of a state as produced by `stepEnc`. -/
def encS (x : Nat) : Nat := Nat.lor (Nat.shiftLeft x 64) (Nat.mod (Nat.shiftLeft x 64) hashP)

/-- AND of the options of a group with `acc`. -/
noncomputable def allAnd (g : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) acc (fun o _ ih => Nat.land o ih) g

/-- AND of all options of all groups with `full`. -/
noncomputable def forcedAll (gs : List (List Nat)) (full : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) full (fun g _ ih => allAnd g ih) gs

/-- Groups paired with their prune masks: the orders forced by all later groups that
make the seed slice inexact. -/
noncomputable def wp (gs : List (List Nat)) (full bad : Nat) : List (List Nat × Nat) :=
  List.rec (motive := fun _ => List (List Nat × Nat)) []
    (fun g rest ih => (g, Nat.land (forcedAll rest full) bad) :: ih) gs

/-- The pre-shifted mask of the seed block's orders outside the seed. -/
def badMask (oSeed seed : Nat) : Nat := Nat.shiftLeft (Nat.xor m720' seed) (Nat.add oSeed 64)

/-- Frontier leaf test: the decoded state is a key of `F`. -/
noncomputable def leafF (F : KTree) (e : Nat) : Bool := Bool.not (Nat.beq (F.find (Nat.shiftRight e 64)) 0)

end CDCert.K6
