/-
CDCert.K6.Seven.C7D — GENERATED kernel checks (Claude's generator `mkcheck7c.py`) of the
seven-level option data, chunked: positions in `copy1`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.Opts
import CDCert.K6.Lex7
import CDCert.K6.DefsK7
import CDCert.K6.Idx7
import CDCert.K6.ChunkEq

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem idx1_copy1_len1 : (copy1.map idx1).length = 5040 := by decide +kernel
theorem idx1_copy1_len2 : (List.range 5040).length = 5040 := by decide +kernel
theorem idx1_copy1_c0 : ((copy1.map idx1).drop 0).take 252 = ((List.range 5040).drop 0).take 252 := by
  decide +kernel
theorem idx1_copy1_c1 : ((copy1.map idx1).drop 252).take 252 = ((List.range 5040).drop 252).take 252 := by
  decide +kernel
theorem idx1_copy1_c2 : ((copy1.map idx1).drop 504).take 252 = ((List.range 5040).drop 504).take 252 := by
  decide +kernel
theorem idx1_copy1_c3 : ((copy1.map idx1).drop 756).take 252 = ((List.range 5040).drop 756).take 252 := by
  decide +kernel
theorem idx1_copy1_c4 : ((copy1.map idx1).drop 1008).take 252 = ((List.range 5040).drop 1008).take 252 := by
  decide +kernel
theorem idx1_copy1_c5 : ((copy1.map idx1).drop 1260).take 252 = ((List.range 5040).drop 1260).take 252 := by
  decide +kernel
theorem idx1_copy1_c6 : ((copy1.map idx1).drop 1512).take 252 = ((List.range 5040).drop 1512).take 252 := by
  decide +kernel
theorem idx1_copy1_c7 : ((copy1.map idx1).drop 1764).take 252 = ((List.range 5040).drop 1764).take 252 := by
  decide +kernel
theorem idx1_copy1_c8 : ((copy1.map idx1).drop 2016).take 252 = ((List.range 5040).drop 2016).take 252 := by
  decide +kernel
theorem idx1_copy1_c9 : ((copy1.map idx1).drop 2268).take 252 = ((List.range 5040).drop 2268).take 252 := by
  decide +kernel
theorem idx1_copy1_c10 : ((copy1.map idx1).drop 2520).take 252 = ((List.range 5040).drop 2520).take 252 := by
  decide +kernel
theorem idx1_copy1_c11 : ((copy1.map idx1).drop 2772).take 252 = ((List.range 5040).drop 2772).take 252 := by
  decide +kernel
theorem idx1_copy1_c12 : ((copy1.map idx1).drop 3024).take 252 = ((List.range 5040).drop 3024).take 252 := by
  decide +kernel
theorem idx1_copy1_c13 : ((copy1.map idx1).drop 3276).take 252 = ((List.range 5040).drop 3276).take 252 := by
  decide +kernel
theorem idx1_copy1_c14 : ((copy1.map idx1).drop 3528).take 252 = ((List.range 5040).drop 3528).take 252 := by
  decide +kernel
theorem idx1_copy1_c15 : ((copy1.map idx1).drop 3780).take 252 = ((List.range 5040).drop 3780).take 252 := by
  decide +kernel
theorem idx1_copy1_c16 : ((copy1.map idx1).drop 4032).take 252 = ((List.range 5040).drop 4032).take 252 := by
  decide +kernel
theorem idx1_copy1_c17 : ((copy1.map idx1).drop 4284).take 252 = ((List.range 5040).drop 4284).take 252 := by
  decide +kernel
theorem idx1_copy1_c18 : ((copy1.map idx1).drop 4536).take 252 = ((List.range 5040).drop 4536).take 252 := by
  decide +kernel
theorem idx1_copy1_c19 : ((copy1.map idx1).drop 4788).take 252 = ((List.range 5040).drop 4788).take 252 := by
  decide +kernel

theorem idx1_copy1 : copy1.map idx1 = List.range 5040 := by
  apply list_eq_of_chunks _ _ 252 20 (by decide) idx1_copy1_len1 idx1_copy1_len2
  intro i hi
  match i, hi with
  | 0, _ => exact idx1_copy1_c0
  | 1, _ => exact idx1_copy1_c1
  | 2, _ => exact idx1_copy1_c2
  | 3, _ => exact idx1_copy1_c3
  | 4, _ => exact idx1_copy1_c4
  | 5, _ => exact idx1_copy1_c5
  | 6, _ => exact idx1_copy1_c6
  | 7, _ => exact idx1_copy1_c7
  | 8, _ => exact idx1_copy1_c8
  | 9, _ => exact idx1_copy1_c9
  | 10, _ => exact idx1_copy1_c10
  | 11, _ => exact idx1_copy1_c11
  | 12, _ => exact idx1_copy1_c12
  | 13, _ => exact idx1_copy1_c13
  | 14, _ => exact idx1_copy1_c14
  | 15, _ => exact idx1_copy1_c15
  | 16, _ => exact idx1_copy1_c16
  | 17, _ => exact idx1_copy1_c17
  | 18, _ => exact idx1_copy1_c18
  | 19, _ => exact idx1_copy1_c19
  | k + 20, h => exact absurd h (by omega)

end CDCert.K6
