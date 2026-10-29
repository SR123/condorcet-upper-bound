/-
CDCert.Examples — finite regression examples, all proved by ordinary `decide`
(kernel evaluation; no `native_decide`, no compiler trust).

Orders on `{0, …, n-1}` are lists from top to bottom. A triple `T = [a, b, c]`
(with `a < b < c`) is a constraint group; its options are never conditions
`x N p` ("`x` is never in position `p` among `T`", positions 0/1/2 =
top/middle/bottom). `allNever` gives all nine; `peakPit` the six never-top /
never-bottom ones.

These are regression tests of the generic machinery on a concrete encoding.
This module tests the generic list encoding. Its connection to semantic
Condorcet domains is supplied in CDCert.Bridge, using the characterisation
proved in Condorcet.TripleCharacterization.
Expected values were computed independently in Python before being checked:
n = 3: 9 domains of size 4 (6 peak-pit); n = 4 peak-pit: 733 distinct domains,
maximum size 9, attained 24 times; exact top-3 slice examples: 108 (all nine
options) and 15 (peak-pit).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.Slice
import CDCert.RowCheck

namespace CDCert.Examples

set_option maxRecDepth 100000

/-- Insert `x` at every position of a list. -/
def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- All permutations of a list. -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

/-- The linear orders on `{0, …, n-1}`, each written from top to bottom. -/
def orders (n : Nat) : List (List Nat) := perms (List.range n)

/-- Position (0 = top) of `x` among the members of `T` in the order `L`. -/
def posIn (T L : List Nat) (x : Nat) : Nat :=
  (L.filter (fun y => decide (y ∈ T))).idxOf x

/-- Never condition `x N p` on the triple `T`. -/
def never (T : List Nat) (x p : Nat) : Opt (List Nat) := fun L => posIn T L x != p

/-- The 3-element subsets of `{0, …, n-1}`, as increasing lists. -/
def triples (n : Nat) : List (List Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (List.range n).flatMap fun c => if a < b ∧ b < c then [[a, b, c]] else []

/-- All nine never conditions of a triple. -/
def allNever (T : List Nat) : Group (List Nat) :=
  T.flatMap fun x => [0, 1, 2].map (never T x)

/-- The six peak-pit never conditions (never top, never bottom). -/
def peakPit (T : List Nat) : Group (List Nat) :=
  T.flatMap fun x => [0, 2].map (never T x)

def groupsAll (n : Nat) : List (Group (List Nat)) := (triples n).map allNever
def groupsPP (n : Nat) : List (Group (List Nat)) := (triples n).map peakPit

/-- Endpoint region: alternative `a` is ranked first. -/
def topIs (a : Nat) : Opt (List Nat) := fun L => L.head? == some a

/-! ### The universe -/

example : (orders 3).length = 6 := by decide
example : (orders 4).length = 24 := by decide
example : (orders 4).Nodup := by decide
example : (triples 4) = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]] := by decide
example : (orders 3).all (fun L => (allNever [0, 1, 2]).all
    (fun o => o L) == false) = true := by decide

/-! ### Enumeration, n = 3 -/

example : (enumerate (groupsAll 3) (orders 3)).length = 9 := by decide
example : (enumerate (groupsAll 3) (orders 3)).all (fun D => D.length == 4) = true := by decide
example : (enumerate (groupsPP 3) (orders 3)).length = 6 := by decide

/-! ### Required / exact slice and pruning, n = 4 -/

/-- The top-3 slice of a maximum domain. -/
def S4 : List (List Nat) := [[3, 2, 0, 1], [3, 2, 1, 0]]

example : (enumerateExact (topIs 3) S4 (groupsAll 4) (orders 4)).length = 108 := by decide
example : (enumerateExact (topIs 3) S4 (groupsPP 4) (orders 4)).length = 15 := by decide
example : (enumerateExactDFS (topIs 3) S4 (groupsPP 4) (orders 4)).length = 15 := by decide
/-- Required-slice filtering leaves 3, 3, 4, 4 peak-pit options on the four triples. -/
example : (requireSlice S4 (groupsPP 4)).map List.length = [3, 3, 4, 4] := by decide

/-- The pruning test really fires: on the last level, 18 of the 36 states
reached in the peak-pit run are pruned (as in the Python simulation). -/
def prunedAtLastLevel : Nat :=
  let gs := requireSlice S4 (groupsPP 4)
  let s1 := dedup ([orders 4].flatMap (expand (gs.getD 0 [])))
  let s2 := dedup (s1.flatMap (expand (gs.getD 1 [])))
  let s3 := dedup (s2.flatMap (expand (gs.getD 2 [])))
  (s3.filter (fun D => pruneForbidden (topIs 3) S4 (gs.drop 3) D)).length

example : prunedAtLastLevel = 18 := by decide

/-! ### Row checking -/

open CDCert.Rows

/-- Certificate `3 x₀ - 2 x₁ + x₂ - 1 ≥ 0`. -/
def cert0 : Cert := ⟨[3, -2, 1], -1⟩

example : checkRows cert0 [[1, 1, 0], [2, 1, -1], [0, 0, 1]] = true := by decide
/-- A negative residual (`-3`) is rejected. -/
example : checkRows cert0 [[0, 1, 0]] = false := by decide
/-- A short row is rejected: a truncating `zipWith` dot product would have
computed `3 - 2 - 1 = 0` and accepted it. -/
example : checkRows cert0 [[1, 1]] = false := by decide
/-- A long row is rejected too. -/
example : checkRows cert0 [[1, 1, 0, 5]] = false := by decide

/-- From a kernel-checked row list to a semantic statement about residuals. -/
theorem cert0_rows_nonneg :
    ∀ f, f ∈ ([[1, 1, 0], [2, 1, -1], [0, 0, 1]] : List (List Int)) → 0 ≤ residual cert0 f :=
  fun f hf => (checkRows_sound (by decide) f hf).2

end CDCert.Examples
