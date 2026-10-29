/-
CDCert.K6.Idx7 — positions of orders in `copy1` and `copy3`, and the gather that
rebuilds all three copies of a seven-level mask from one copy.

* `idx6 M`: position of a six-order in `baseB 5` (`120 * last + lexIdx` of the rest);
* `idx1 M`, `idx3 M`: positions of a seven-order in `copy1` (by last label) and in
  `copy3` (by first label);
* `gRow`, `gath`: gather bits of a mask by a list of 42 rows of 120 source positions;
  `expand1`, `expand3`: the 15120-bit three-copy mask from the `copy1` / `copy3` mask.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Defs5
import CDCert.Deletion

namespace CDCert.K6

open CDCert CDCert.ListOrder

/-- Position of a six-order in `baseB 5`. -/
def idx6 (M : List Nat) : Nat := 120 * M.getLastD 0 + lexIdx (deleteLabel (M.getLastD 0) M)

/-- Position of a seven-order in `copy1`. -/
def idx1 (M : List Nat) : Nat := 720 * M.getLastD 0 + idx6 (deleteLabel (M.getLastD 0) M)

/-- Position of a seven-order in `copy3`. -/
def idx3 (M : List Nat) : Nat := 720 * M.headD 0 + idx6 (deleteLabel (M.headD 0) M)

/-- Gather a row: bit `j` is bit `row[j]` of `s`. -/
noncomputable def gRow (row : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun i _ ih => Nat.add (Nat.land (Nat.shiftRight s i) 1) (Nat.mul 2 ih)) row

/-- Gather by blocks of 120: bit `120 b + j` is bit `rows[b][j]` of `s`. -/
noncomputable def gath (rows : List (List Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun row _ ih => Nat.lor (gRow row s) (Nat.shiftLeft ih 120)) rows

/-- Gather a row of `(offset, bit)` pairs: bit `j` is bit `bit_j` of the 120-bit block of `s`
at `offset_j` (the blocks are shared between entries, so the kernel extracts each once). -/
noncomputable def gRow2 (row : List (Nat × Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => Nat.add (Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight s p.1)
      (nat_lit 1329227995784915872903807060280344575)) p.2) 1) (Nat.mul 2 ih)) row

/-- Gather by blocks of 120 with `(offset, bit)` rows. -/
noncomputable def gath2 (rows : List (List (Nat × Nat))) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun row _ ih => Nat.lor (gRow2 row s) (Nat.shiftLeft ih 120)) rows

/-- One group of a gather: bits `j` from bit `r` of the 120-bit block of `s` at offset `o`. -/
noncomputable def gGroup (o : Nat) (es : List (Nat × Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight s o)
      (nat_lit 1329227995784915872903807060280344575)) e.2) 1) e.1) ih) es

/-- A target block gathered from groups. -/
noncomputable def gBlk (gs : List (Nat × List (Nat × Nat))) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun g _ ih => Nat.lor (gGroup g.1 g.2 s) ih) gs

/-- Gather by target blocks of 120, each from groups sharing a source block. -/
noncomputable def gath3 (rows : List (List (Nat × List (Nat × Nat)))) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun blk _ ih => Nat.lor (gBlk blk s) (Nat.shiftLeft ih 120)) rows

/-- Sources of target bit `j` of a gather block. -/
def srcOf (blk : List (Nat × List (Nat × Nat))) (j : Nat) : List Nat :=
  blk.flatMap (fun g => g.2.filterMap (fun e => if e.1 = j then some (g.1 + e.2) else none))

/-- The sources of all target bits, block by block. -/
def gatherSpec (rows : List (List (Nat × List (Nat × Nat)))) : List (List Nat) :=
  rows.flatMap (fun blk => (List.range 120).map (fun j => srcOf blk j))

/-- All target and source bits of a gather are below 120. -/
def gatherOK (rows : List (List (Nat × List (Nat × Nat)))) : Bool :=
  rows.all (fun blk => blk.all (fun g => g.2.all (fun e => decide (e.1 < 120) && decide (e.2 < 120))))

end CDCert.K6
