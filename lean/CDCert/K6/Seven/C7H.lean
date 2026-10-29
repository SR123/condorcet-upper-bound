/-
CDCert.K6.Seven.C7H — GENERATED kernel checks (Claude's generator `mkcheck7c.py`) of the
seven-level option data, chunked: the gather rows `g31` read `copy1` at the positions `idx3`.

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

theorem g31_spec_len1 : (gatherSpec g31).length = 5040 := by decide +kernel
theorem g31_spec_len2 : ((copy1.map idx3).map (fun x => [x])).length = 5040 := by decide +kernel
theorem g31_spec_c0 : ((gatherSpec g31).drop 0).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 0).take 240 := by
  decide +kernel
theorem g31_spec_c1 : ((gatherSpec g31).drop 240).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 240).take 240 := by
  decide +kernel
theorem g31_spec_c2 : ((gatherSpec g31).drop 480).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 480).take 240 := by
  decide +kernel
theorem g31_spec_c3 : ((gatherSpec g31).drop 720).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 720).take 240 := by
  decide +kernel
theorem g31_spec_c4 : ((gatherSpec g31).drop 960).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 960).take 240 := by
  decide +kernel
theorem g31_spec_c5 : ((gatherSpec g31).drop 1200).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 1200).take 240 := by
  decide +kernel
theorem g31_spec_c6 : ((gatherSpec g31).drop 1440).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 1440).take 240 := by
  decide +kernel
theorem g31_spec_c7 : ((gatherSpec g31).drop 1680).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 1680).take 240 := by
  decide +kernel
theorem g31_spec_c8 : ((gatherSpec g31).drop 1920).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 1920).take 240 := by
  decide +kernel
theorem g31_spec_c9 : ((gatherSpec g31).drop 2160).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 2160).take 240 := by
  decide +kernel
theorem g31_spec_c10 : ((gatherSpec g31).drop 2400).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 2400).take 240 := by
  decide +kernel
theorem g31_spec_c11 : ((gatherSpec g31).drop 2640).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 2640).take 240 := by
  decide +kernel
theorem g31_spec_c12 : ((gatherSpec g31).drop 2880).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 2880).take 240 := by
  decide +kernel
theorem g31_spec_c13 : ((gatherSpec g31).drop 3120).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 3120).take 240 := by
  decide +kernel
theorem g31_spec_c14 : ((gatherSpec g31).drop 3360).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 3360).take 240 := by
  decide +kernel
theorem g31_spec_c15 : ((gatherSpec g31).drop 3600).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 3600).take 240 := by
  decide +kernel
theorem g31_spec_c16 : ((gatherSpec g31).drop 3840).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 3840).take 240 := by
  decide +kernel
theorem g31_spec_c17 : ((gatherSpec g31).drop 4080).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 4080).take 240 := by
  decide +kernel
theorem g31_spec_c18 : ((gatherSpec g31).drop 4320).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 4320).take 240 := by
  decide +kernel
theorem g31_spec_c19 : ((gatherSpec g31).drop 4560).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 4560).take 240 := by
  decide +kernel
theorem g31_spec_c20 : ((gatherSpec g31).drop 4800).take 240 = (((copy1.map idx3).map (fun x => [x])).drop 4800).take 240 := by
  decide +kernel

theorem g31_spec : gatherSpec g31 = (copy1.map idx3).map (fun x => [x]) := by
  apply list_eq_of_chunks _ _ 240 21 (by decide) g31_spec_len1 g31_spec_len2
  intro i hi
  match i, hi with
  | 0, _ => exact g31_spec_c0
  | 1, _ => exact g31_spec_c1
  | 2, _ => exact g31_spec_c2
  | 3, _ => exact g31_spec_c3
  | 4, _ => exact g31_spec_c4
  | 5, _ => exact g31_spec_c5
  | 6, _ => exact g31_spec_c6
  | 7, _ => exact g31_spec_c7
  | 8, _ => exact g31_spec_c8
  | 9, _ => exact g31_spec_c9
  | 10, _ => exact g31_spec_c10
  | 11, _ => exact g31_spec_c11
  | 12, _ => exact g31_spec_c12
  | 13, _ => exact g31_spec_c13
  | 14, _ => exact g31_spec_c14
  | 15, _ => exact g31_spec_c15
  | 16, _ => exact g31_spec_c16
  | 17, _ => exact g31_spec_c17
  | 18, _ => exact g31_spec_c18
  | 19, _ => exact g31_spec_c19
  | 20, _ => exact g31_spec_c20
  | k + 21, h => exact absurd h (by omega)

theorem g31_ok : gatherOK g31 = true := by decide +kernel

theorem g31_eq : gatherSpec g31 = (copy1.map idx3).map (fun x => [x]) ∧ gatherOK g31 = true :=
  ⟨g31_spec, g31_ok⟩

end CDCert.K6
