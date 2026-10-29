/-
CDCert.K6.Lex — lexicographic enumeration of orders and the bottom- and top-indexed
bases used by the six-level kernel check.

* `lexOrders k`: the permutations of `0..k-1` in lexicographic order (the order
  of Python's `itertools.permutations(range(k))`, used to index masks);
* `baseB k`, `baseT k`: the orders on `k+1` labels grouped by their last
  (resp. first) label `x`, each block listing `L.map (up x) ++ [x]`
  (resp. `x :: L.map (up x)`) for `L` in `lexOrders k`;
* `base12 = baseB 5 ++ baseT 5`: the base of the combined six-level masks;
* `groupsPF6`: the options introduced with label 5 as list-level options,
  pair groups first (`pairOptions a 5`, `a < 5`), then the triple groups of
  `groupsNew 5` (extreme laws on `(a, b, 5)`, `a < b < 5`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.Deletion
import CDCert.Extension

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

/-- Permutations of `l` of length `n` (`n = l.length`) in lexicographic order of
first elements when `l` is increasing. -/
def lexPermsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, l => l.flatMap (fun x => (lexPermsAux n (l.erase x)).map (x :: ·))

/-- The orders on `0..k-1` in lexicographic order. -/
def lexOrders (k : Nat) : List (List Nat) := lexPermsAux k (List.range k)

/-- Bottom-indexed base on `k+1` labels: block `x` lists `L.map (up x) ++ [x]`. -/
def baseB (k : Nat) : List (List Nat) :=
  (List.range (k + 1)).flatMap (fun x => (lexOrders k).map (fun L => L.map (up x) ++ [x]))

/-- Top-indexed base on `k+1` labels: block `x` lists `x :: L.map (up x)`. -/
def baseT (k : Nat) : List (List Nat) :=
  (List.range (k + 1)).flatMap (fun x => (lexOrders k).map (fun L => x :: L.map (up x)))

/-- The base of the combined six-level masks. -/
def base12 : List (List Nat) := baseB 5 ++ baseT 5

/-- The options introduced with label 5, pair groups first. -/
def groupsPF6 : List (Group (List Nat)) :=
  (List.range 5).map (fun a => pairOptions a 5) ++
  (newTriples 5).map (fun t => lawsExtreme.map (holdsL t.1 t.2.1 t.2.2))

end CDCert.K6
