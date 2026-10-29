/-
CDCert.K6.Seven.C7A — GENERATED kernel checks (Claude's generator `mkcheck7c.py`) of the
seven-level option data, chunked: packed comparisons of `copy1`.

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

theorem cm7_0_eq_len1 : (cm7_0).length = 5040 := by decide +kernel
theorem cm7_0_eq_len2 : (copy1.map cmpOf).length = 5040 := by decide +kernel
theorem cm7_0_eq_c0 : ((cm7_0).drop 0).take 252 = ((copy1.map cmpOf).drop 0).take 252 := by
  decide +kernel
theorem cm7_0_eq_c1 : ((cm7_0).drop 252).take 252 = ((copy1.map cmpOf).drop 252).take 252 := by
  decide +kernel
theorem cm7_0_eq_c2 : ((cm7_0).drop 504).take 252 = ((copy1.map cmpOf).drop 504).take 252 := by
  decide +kernel
theorem cm7_0_eq_c3 : ((cm7_0).drop 756).take 252 = ((copy1.map cmpOf).drop 756).take 252 := by
  decide +kernel
theorem cm7_0_eq_c4 : ((cm7_0).drop 1008).take 252 = ((copy1.map cmpOf).drop 1008).take 252 := by
  decide +kernel
theorem cm7_0_eq_c5 : ((cm7_0).drop 1260).take 252 = ((copy1.map cmpOf).drop 1260).take 252 := by
  decide +kernel
theorem cm7_0_eq_c6 : ((cm7_0).drop 1512).take 252 = ((copy1.map cmpOf).drop 1512).take 252 := by
  decide +kernel
theorem cm7_0_eq_c7 : ((cm7_0).drop 1764).take 252 = ((copy1.map cmpOf).drop 1764).take 252 := by
  decide +kernel
theorem cm7_0_eq_c8 : ((cm7_0).drop 2016).take 252 = ((copy1.map cmpOf).drop 2016).take 252 := by
  decide +kernel
theorem cm7_0_eq_c9 : ((cm7_0).drop 2268).take 252 = ((copy1.map cmpOf).drop 2268).take 252 := by
  decide +kernel
theorem cm7_0_eq_c10 : ((cm7_0).drop 2520).take 252 = ((copy1.map cmpOf).drop 2520).take 252 := by
  decide +kernel
theorem cm7_0_eq_c11 : ((cm7_0).drop 2772).take 252 = ((copy1.map cmpOf).drop 2772).take 252 := by
  decide +kernel
theorem cm7_0_eq_c12 : ((cm7_0).drop 3024).take 252 = ((copy1.map cmpOf).drop 3024).take 252 := by
  decide +kernel
theorem cm7_0_eq_c13 : ((cm7_0).drop 3276).take 252 = ((copy1.map cmpOf).drop 3276).take 252 := by
  decide +kernel
theorem cm7_0_eq_c14 : ((cm7_0).drop 3528).take 252 = ((copy1.map cmpOf).drop 3528).take 252 := by
  decide +kernel
theorem cm7_0_eq_c15 : ((cm7_0).drop 3780).take 252 = ((copy1.map cmpOf).drop 3780).take 252 := by
  decide +kernel
theorem cm7_0_eq_c16 : ((cm7_0).drop 4032).take 252 = ((copy1.map cmpOf).drop 4032).take 252 := by
  decide +kernel
theorem cm7_0_eq_c17 : ((cm7_0).drop 4284).take 252 = ((copy1.map cmpOf).drop 4284).take 252 := by
  decide +kernel
theorem cm7_0_eq_c18 : ((cm7_0).drop 4536).take 252 = ((copy1.map cmpOf).drop 4536).take 252 := by
  decide +kernel
theorem cm7_0_eq_c19 : ((cm7_0).drop 4788).take 252 = ((copy1.map cmpOf).drop 4788).take 252 := by
  decide +kernel

theorem cm7_0_eq : cm7_0 = copy1.map cmpOf := by
  apply list_eq_of_chunks _ _ 252 20 (by decide) cm7_0_eq_len1 cm7_0_eq_len2
  intro i hi
  match i, hi with
  | 0, _ => exact cm7_0_eq_c0
  | 1, _ => exact cm7_0_eq_c1
  | 2, _ => exact cm7_0_eq_c2
  | 3, _ => exact cm7_0_eq_c3
  | 4, _ => exact cm7_0_eq_c4
  | 5, _ => exact cm7_0_eq_c5
  | 6, _ => exact cm7_0_eq_c6
  | 7, _ => exact cm7_0_eq_c7
  | 8, _ => exact cm7_0_eq_c8
  | 9, _ => exact cm7_0_eq_c9
  | 10, _ => exact cm7_0_eq_c10
  | 11, _ => exact cm7_0_eq_c11
  | 12, _ => exact cm7_0_eq_c12
  | 13, _ => exact cm7_0_eq_c13
  | 14, _ => exact cm7_0_eq_c14
  | 15, _ => exact cm7_0_eq_c15
  | 16, _ => exact cm7_0_eq_c16
  | 17, _ => exact cm7_0_eq_c17
  | 18, _ => exact cm7_0_eq_c18
  | 19, _ => exact cm7_0_eq_c19
  | k + 20, h => exact absurd h (by omega)

end CDCert.K6
