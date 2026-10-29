/-
CDCert.K6.Tab.CheckAux — kernel checks of the auxiliary table data (Claude's generator
`mktab.py`):

* `sw5_eq`, `sw53_eq`: the swap rows are `lexIdx (swapAt j L)` over `lexOrders 5`;
* `idxB_baseB`: `idxB` is the position in `baseB 5`;
* `rowB_s_eq`: each witness row is `idxB (rlab σ M)` over `baseB 5` for its permutation;
* `excWit_i`: each of the 204 exceptional masks is mapped by its witness row onto one of
  the fourteen exceptional types;
* `exc6_keys`: the keys of `exc6` are exactly `exc6keys`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Tab.Aux
import CDCert.K6.Defs5
import CDCert.K6.Lex5
import CDCert.K6.Data6
import CDCert.Deletion

namespace CDCert.K6

open CDCert CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000
set_option Elab.async false

/-- Index of a six-order in `baseB 5`: `120 * last + lexIdx (deletion of last)`. -/
def idxB (M : List Nat) : Nat := 120 * M.getLastD 0 + lexIdx (deleteLabel (M.getLastD 0) M)

/-- Keys of a tree, in order (as `KTree.keys` of `CDCert.K6.MaskSem`; kept separate so
that this check does not depend on the proof layer). -/
noncomputable def KTree.keysC (t : KTree) : List Nat :=
  KTree.rec (motive := fun _ => List Nat) [] (fun _ key _ _ ihl ihr => ihl ++ key :: ihr) t

theorem sw5_eq : sw5 = (lexOrders 5).map (fun L => (List.range 4).map (fun j => lexIdx (swapAt j L))) := by
  decide +kernel

theorem sw53_eq : sw53 = (lexOrders 5).map (fun L => lexIdx (swapAt 3 L)) := by
  decide +kernel

theorem idxB_baseB : (baseB 5).map idxB = List.range 720 := by
  decide +kernel

theorem rowB_0_eq : rowB_0 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_1_eq : rowB_1 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 3, 5, 4] M)) := by
  decide +kernel

theorem rowB_2_eq : rowB_2 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 4, 3, 5] M)) := by
  decide +kernel

theorem rowB_3_eq : rowB_3 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_4_eq : rowB_4 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_5_eq : rowB_5 = (baseB 5).map (fun M => idxB (rlab [0, 1, 2, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_6_eq : rowB_6 = (baseB 5).map (fun M => idxB (rlab [0, 1, 3, 2, 4, 5] M)) := by
  decide +kernel

theorem rowB_7_eq : rowB_7 = (baseB 5).map (fun M => idxB (rlab [0, 1, 3, 2, 5, 4] M)) := by
  decide +kernel

theorem rowB_9_eq : rowB_9 = (baseB 5).map (fun M => idxB (rlab [0, 1, 3, 4, 5, 2] M)) := by
  decide +kernel

theorem rowB_11_eq : rowB_11 = (baseB 5).map (fun M => idxB (rlab [0, 1, 3, 5, 4, 2] M)) := by
  decide +kernel

theorem rowB_13_eq : rowB_13 = (baseB 5).map (fun M => idxB (rlab [0, 1, 4, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_15_eq : rowB_15 = (baseB 5).map (fun M => idxB (rlab [0, 1, 4, 3, 5, 2] M)) := by
  decide +kernel

theorem rowB_16_eq : rowB_16 = (baseB 5).map (fun M => idxB (rlab [0, 1, 4, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_17_eq : rowB_17 = (baseB 5).map (fun M => idxB (rlab [0, 1, 4, 5, 3, 2] M)) := by
  decide +kernel

theorem rowB_18_eq : rowB_18 = (baseB 5).map (fun M => idxB (rlab [0, 1, 5, 2, 3, 4] M)) := by
  decide +kernel

theorem rowB_19_eq : rowB_19 = (baseB 5).map (fun M => idxB (rlab [0, 1, 5, 2, 4, 3] M)) := by
  decide +kernel

theorem rowB_21_eq : rowB_21 = (baseB 5).map (fun M => idxB (rlab [0, 1, 5, 3, 4, 2] M)) := by
  decide +kernel

theorem rowB_22_eq : rowB_22 = (baseB 5).map (fun M => idxB (rlab [0, 1, 5, 4, 2, 3] M)) := by
  decide +kernel

theorem rowB_23_eq : rowB_23 = (baseB 5).map (fun M => idxB (rlab [0, 1, 5, 4, 3, 2] M)) := by
  decide +kernel

theorem rowB_24_eq : rowB_24 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_25_eq : rowB_25 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 3, 5, 4] M)) := by
  decide +kernel

theorem rowB_26_eq : rowB_26 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 4, 3, 5] M)) := by
  decide +kernel

theorem rowB_27_eq : rowB_27 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_28_eq : rowB_28 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_29_eq : rowB_29 = (baseB 5).map (fun M => idxB (rlab [0, 2, 1, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_30_eq : rowB_30 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 1, 4, 5] M)) := by
  decide +kernel

theorem rowB_31_eq : rowB_31 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 1, 5, 4] M)) := by
  decide +kernel

theorem rowB_32_eq : rowB_32 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 4, 1, 5] M)) := by
  decide +kernel

theorem rowB_33_eq : rowB_33 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 4, 5, 1] M)) := by
  decide +kernel

theorem rowB_34_eq : rowB_34 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 5, 1, 4] M)) := by
  decide +kernel

theorem rowB_35_eq : rowB_35 = (baseB 5).map (fun M => idxB (rlab [0, 2, 3, 5, 4, 1] M)) := by
  decide +kernel

theorem rowB_36_eq : rowB_36 = (baseB 5).map (fun M => idxB (rlab [0, 2, 4, 1, 3, 5] M)) := by
  decide +kernel

theorem rowB_37_eq : rowB_37 = (baseB 5).map (fun M => idxB (rlab [0, 2, 4, 1, 5, 3] M)) := by
  decide +kernel

theorem rowB_39_eq : rowB_39 = (baseB 5).map (fun M => idxB (rlab [0, 2, 4, 3, 5, 1] M)) := by
  decide +kernel

theorem rowB_40_eq : rowB_40 = (baseB 5).map (fun M => idxB (rlab [0, 2, 4, 5, 1, 3] M)) := by
  decide +kernel

theorem rowB_41_eq : rowB_41 = (baseB 5).map (fun M => idxB (rlab [0, 2, 4, 5, 3, 1] M)) := by
  decide +kernel

theorem rowB_42_eq : rowB_42 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 1, 3, 4] M)) := by
  decide +kernel

theorem rowB_43_eq : rowB_43 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 1, 4, 3] M)) := by
  decide +kernel

theorem rowB_44_eq : rowB_44 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 3, 1, 4] M)) := by
  decide +kernel

theorem rowB_45_eq : rowB_45 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 3, 4, 1] M)) := by
  decide +kernel

theorem rowB_46_eq : rowB_46 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 4, 1, 3] M)) := by
  decide +kernel

theorem rowB_47_eq : rowB_47 = (baseB 5).map (fun M => idxB (rlab [0, 2, 5, 4, 3, 1] M)) := by
  decide +kernel

theorem rowB_51_eq : rowB_51 = (baseB 5).map (fun M => idxB (rlab [0, 3, 1, 4, 5, 2] M)) := by
  decide +kernel

theorem rowB_57_eq : rowB_57 = (baseB 5).map (fun M => idxB (rlab [0, 3, 2, 4, 5, 1] M)) := by
  decide +kernel

theorem rowB_59_eq : rowB_59 = (baseB 5).map (fun M => idxB (rlab [0, 3, 2, 5, 4, 1] M)) := by
  decide +kernel

theorem rowB_73_eq : rowB_73 = (baseB 5).map (fun M => idxB (rlab [0, 4, 1, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_76_eq : rowB_76 = (baseB 5).map (fun M => idxB (rlab [0, 4, 1, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_79_eq : rowB_79 = (baseB 5).map (fun M => idxB (rlab [0, 4, 2, 1, 5, 3] M)) := by
  decide +kernel

theorem rowB_82_eq : rowB_82 = (baseB 5).map (fun M => idxB (rlab [0, 4, 2, 5, 1, 3] M)) := by
  decide +kernel

theorem rowB_90_eq : rowB_90 = (baseB 5).map (fun M => idxB (rlab [0, 4, 5, 1, 2, 3] M)) := by
  decide +kernel

theorem rowB_92_eq : rowB_92 = (baseB 5).map (fun M => idxB (rlab [0, 4, 5, 2, 1, 3] M)) := by
  decide +kernel

theorem rowB_96_eq : rowB_96 = (baseB 5).map (fun M => idxB (rlab [0, 5, 1, 2, 3, 4] M)) := by
  decide +kernel

theorem rowB_97_eq : rowB_97 = (baseB 5).map (fun M => idxB (rlab [0, 5, 1, 2, 4, 3] M)) := by
  decide +kernel

theorem rowB_100_eq : rowB_100 = (baseB 5).map (fun M => idxB (rlab [0, 5, 1, 4, 2, 3] M)) := by
  decide +kernel

theorem rowB_102_eq : rowB_102 = (baseB 5).map (fun M => idxB (rlab [0, 5, 2, 1, 3, 4] M)) := by
  decide +kernel

theorem rowB_103_eq : rowB_103 = (baseB 5).map (fun M => idxB (rlab [0, 5, 2, 1, 4, 3] M)) := by
  decide +kernel

theorem rowB_105_eq : rowB_105 = (baseB 5).map (fun M => idxB (rlab [0, 5, 2, 3, 4, 1] M)) := by
  decide +kernel

theorem rowB_106_eq : rowB_106 = (baseB 5).map (fun M => idxB (rlab [0, 5, 2, 4, 1, 3] M)) := by
  decide +kernel

theorem rowB_107_eq : rowB_107 = (baseB 5).map (fun M => idxB (rlab [0, 5, 2, 4, 3, 1] M)) := by
  decide +kernel

theorem rowB_114_eq : rowB_114 = (baseB 5).map (fun M => idxB (rlab [0, 5, 4, 1, 2, 3] M)) := by
  decide +kernel

theorem rowB_120_eq : rowB_120 = (baseB 5).map (fun M => idxB (rlab [1, 0, 2, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_121_eq : rowB_121 = (baseB 5).map (fun M => idxB (rlab [1, 0, 2, 3, 5, 4] M)) := by
  decide +kernel

theorem rowB_123_eq : rowB_123 = (baseB 5).map (fun M => idxB (rlab [1, 0, 2, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_124_eq : rowB_124 = (baseB 5).map (fun M => idxB (rlab [1, 0, 2, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_125_eq : rowB_125 = (baseB 5).map (fun M => idxB (rlab [1, 0, 2, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_127_eq : rowB_127 = (baseB 5).map (fun M => idxB (rlab [1, 0, 3, 2, 5, 4] M)) := by
  decide +kernel

theorem rowB_129_eq : rowB_129 = (baseB 5).map (fun M => idxB (rlab [1, 0, 3, 4, 5, 2] M)) := by
  decide +kernel

theorem rowB_131_eq : rowB_131 = (baseB 5).map (fun M => idxB (rlab [1, 0, 3, 5, 4, 2] M)) := by
  decide +kernel

theorem rowB_133_eq : rowB_133 = (baseB 5).map (fun M => idxB (rlab [1, 0, 4, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_135_eq : rowB_135 = (baseB 5).map (fun M => idxB (rlab [1, 0, 4, 3, 5, 2] M)) := by
  decide +kernel

theorem rowB_136_eq : rowB_136 = (baseB 5).map (fun M => idxB (rlab [1, 0, 4, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_137_eq : rowB_137 = (baseB 5).map (fun M => idxB (rlab [1, 0, 4, 5, 3, 2] M)) := by
  decide +kernel

theorem rowB_138_eq : rowB_138 = (baseB 5).map (fun M => idxB (rlab [1, 0, 5, 2, 3, 4] M)) := by
  decide +kernel

theorem rowB_139_eq : rowB_139 = (baseB 5).map (fun M => idxB (rlab [1, 0, 5, 2, 4, 3] M)) := by
  decide +kernel

theorem rowB_141_eq : rowB_141 = (baseB 5).map (fun M => idxB (rlab [1, 0, 5, 3, 4, 2] M)) := by
  decide +kernel

theorem rowB_142_eq : rowB_142 = (baseB 5).map (fun M => idxB (rlab [1, 0, 5, 4, 2, 3] M)) := by
  decide +kernel

theorem rowB_144_eq : rowB_144 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_145_eq : rowB_145 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 3, 5, 4] M)) := by
  decide +kernel

theorem rowB_146_eq : rowB_146 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 4, 3, 5] M)) := by
  decide +kernel

theorem rowB_147_eq : rowB_147 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_148_eq : rowB_148 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_149_eq : rowB_149 = (baseB 5).map (fun M => idxB (rlab [1, 2, 0, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_153_eq : rowB_153 = (baseB 5).map (fun M => idxB (rlab [1, 2, 3, 4, 5, 0] M)) := by
  decide +kernel

theorem rowB_155_eq : rowB_155 = (baseB 5).map (fun M => idxB (rlab [1, 2, 3, 5, 4, 0] M)) := by
  decide +kernel

theorem rowB_159_eq : rowB_159 = (baseB 5).map (fun M => idxB (rlab [1, 2, 4, 3, 5, 0] M)) := by
  decide +kernel

theorem rowB_165_eq : rowB_165 = (baseB 5).map (fun M => idxB (rlab [1, 2, 5, 3, 4, 0] M)) := by
  decide +kernel

theorem rowB_193_eq : rowB_193 = (baseB 5).map (fun M => idxB (rlab [1, 4, 0, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_196_eq : rowB_196 = (baseB 5).map (fun M => idxB (rlab [1, 4, 0, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_217_eq : rowB_217 = (baseB 5).map (fun M => idxB (rlab [1, 5, 0, 2, 4, 3] M)) := by
  decide +kernel

theorem rowB_240_eq : rowB_240 = (baseB 5).map (fun M => idxB (rlab [2, 0, 1, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_241_eq : rowB_241 = (baseB 5).map (fun M => idxB (rlab [2, 0, 1, 3, 5, 4] M)) := by
  decide +kernel

theorem rowB_243_eq : rowB_243 = (baseB 5).map (fun M => idxB (rlab [2, 0, 1, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_244_eq : rowB_244 = (baseB 5).map (fun M => idxB (rlab [2, 0, 1, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_245_eq : rowB_245 = (baseB 5).map (fun M => idxB (rlab [2, 0, 1, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_249_eq : rowB_249 = (baseB 5).map (fun M => idxB (rlab [2, 0, 3, 4, 5, 1] M)) := by
  decide +kernel

theorem rowB_250_eq : rowB_250 = (baseB 5).map (fun M => idxB (rlab [2, 0, 3, 5, 1, 4] M)) := by
  decide +kernel

theorem rowB_251_eq : rowB_251 = (baseB 5).map (fun M => idxB (rlab [2, 0, 3, 5, 4, 1] M)) := by
  decide +kernel

theorem rowB_256_eq : rowB_256 = (baseB 5).map (fun M => idxB (rlab [2, 0, 4, 5, 1, 3] M)) := by
  decide +kernel

theorem rowB_258_eq : rowB_258 = (baseB 5).map (fun M => idxB (rlab [2, 0, 5, 1, 3, 4] M)) := by
  decide +kernel

theorem rowB_259_eq : rowB_259 = (baseB 5).map (fun M => idxB (rlab [2, 0, 5, 1, 4, 3] M)) := by
  decide +kernel

theorem rowB_261_eq : rowB_261 = (baseB 5).map (fun M => idxB (rlab [2, 0, 5, 3, 4, 1] M)) := by
  decide +kernel

theorem rowB_262_eq : rowB_262 = (baseB 5).map (fun M => idxB (rlab [2, 0, 5, 4, 1, 3] M)) := by
  decide +kernel

theorem rowB_263_eq : rowB_263 = (baseB 5).map (fun M => idxB (rlab [2, 0, 5, 4, 3, 1] M)) := by
  decide +kernel

theorem rowB_264_eq : rowB_264 = (baseB 5).map (fun M => idxB (rlab [2, 1, 0, 3, 4, 5] M)) := by
  decide +kernel

theorem rowB_267_eq : rowB_267 = (baseB 5).map (fun M => idxB (rlab [2, 1, 0, 4, 5, 3] M)) := by
  decide +kernel

theorem rowB_268_eq : rowB_268 = (baseB 5).map (fun M => idxB (rlab [2, 1, 0, 5, 3, 4] M)) := by
  decide +kernel

theorem rowB_269_eq : rowB_269 = (baseB 5).map (fun M => idxB (rlab [2, 1, 0, 5, 4, 3] M)) := by
  decide +kernel

theorem rowB_273_eq : rowB_273 = (baseB 5).map (fun M => idxB (rlab [2, 1, 3, 4, 5, 0] M)) := by
  decide +kernel

theorem rowB_275_eq : rowB_275 = (baseB 5).map (fun M => idxB (rlab [2, 1, 3, 5, 4, 0] M)) := by
  decide +kernel

theorem rowB_285_eq : rowB_285 = (baseB 5).map (fun M => idxB (rlab [2, 1, 5, 3, 4, 0] M)) := by
  decide +kernel

theorem rowB_291_eq : rowB_291 = (baseB 5).map (fun M => idxB (rlab [2, 3, 0, 4, 5, 1] M)) := by
  decide +kernel

theorem rowB_293_eq : rowB_293 = (baseB 5).map (fun M => idxB (rlab [2, 3, 0, 5, 4, 1] M)) := by
  decide +kernel

theorem rowB_297_eq : rowB_297 = (baseB 5).map (fun M => idxB (rlab [2, 3, 1, 4, 5, 0] M)) := by
  decide +kernel

theorem rowB_299_eq : rowB_299 = (baseB 5).map (fun M => idxB (rlab [2, 3, 1, 5, 4, 0] M)) := by
  decide +kernel

theorem rowB_411_eq : rowB_411 = (baseB 5).map (fun M => idxB (rlab [3, 2, 0, 4, 5, 1] M)) := by
  decide +kernel

theorem rowB_413_eq : rowB_413 = (baseB 5).map (fun M => idxB (rlab [3, 2, 0, 5, 4, 1] M)) := by
  decide +kernel

theorem rowB_417_eq : rowB_417 = (baseB 5).map (fun M => idxB (rlab [3, 2, 1, 4, 5, 0] M)) := by
  decide +kernel

theorem rowB_481_eq : rowB_481 = (baseB 5).map (fun M => idxB (rlab [4, 0, 1, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_484_eq : rowB_484 = (baseB 5).map (fun M => idxB (rlab [4, 0, 1, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_490_eq : rowB_490 = (baseB 5).map (fun M => idxB (rlab [4, 0, 2, 5, 1, 3] M)) := by
  decide +kernel

theorem rowB_498_eq : rowB_498 = (baseB 5).map (fun M => idxB (rlab [4, 0, 5, 1, 2, 3] M)) := by
  decide +kernel

theorem rowB_505_eq : rowB_505 = (baseB 5).map (fun M => idxB (rlab [4, 1, 0, 2, 5, 3] M)) := by
  decide +kernel

theorem rowB_508_eq : rowB_508 = (baseB 5).map (fun M => idxB (rlab [4, 1, 0, 5, 2, 3] M)) := by
  decide +kernel

theorem rowB_601_eq : rowB_601 = (baseB 5).map (fun M => idxB (rlab [5, 0, 1, 2, 4, 3] M)) := by
  decide +kernel

theorem excWit_0 : relabelI rowB_601 (nat_lit 0xc00f3) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_1 : relabelI rowB_96 (nat_lit 0x30cf000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_2 : relabelI rowB_102 (nat_lit 0xc3c3000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_3 : relabelI rowB_97 (nat_lit 0xc00f3000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_4 : relabelI rowB_100 (nat_lit 0xc303c000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_5 : relabelI rowB_103 (nat_lit 0x300cc3000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_6 : relabelI rowB_114 (nat_lit 0x30cf00000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_7 : relabelI rowB_105 (nat_lit 0x3c0c30000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_8 : relabelI rowB_106 (nat_lit 0xc3300c000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_9 : relabelI rowB_107 (nat_lit 0xcf0030000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_10 : relabelI rowB_217 (nat_lit 0xc00f3000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_11 : relabelI rowB_18 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_12 : relabelI rowB_42 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_13 : relabelI rowB_44 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_14 : relabelI rowB_19 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_15 : relabelI rowB_22 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_16 : relabelI rowB_43 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_17 : relabelI rowB_90 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_18 : relabelI rowB_45 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_19 : relabelI rowB_46 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_20 : relabelI rowB_92 (nat_lit 0xc3c300000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_21 : relabelI rowB_47 (nat_lit 0xcf0030000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_22 : relabelI rowB_138 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_23 : relabelI rowB_258 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_24 : relabelI rowB_139 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_25 : relabelI rowB_142 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_26 : relabelI rowB_259 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_27 : relabelI rowB_498 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_28 : relabelI rowB_261 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_29 : relabelI rowB_262 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_30 : relabelI rowB_263 (nat_lit 0xcf0030000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_31 : relabelI rowB_165 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_32 : relabelI rowB_4 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_33 : relabelI rowB_28 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_34 : relabelI rowB_34 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_35 : relabelI rowB_5 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_36 : relabelI rowB_16 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_37 : relabelI rowB_29 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_38 : relabelI rowB_76 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_39 : relabelI rowB_35 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_40 : relabelI rowB_40 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_41 : relabelI rowB_82 (nat_lit 0xc3c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_42 : relabelI rowB_41 (nat_lit 0xcf0030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_43 : relabelI rowB_124 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_44 : relabelI rowB_244 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_45 : relabelI rowB_250 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_46 : relabelI rowB_125 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_47 : relabelI rowB_136 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_48 : relabelI rowB_23 (nat_lit 0xc303c0c303c0000000000000000000c303c1c303c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_49 : relabelI rowB_17 (nat_lit 0xc303c1c303c0000000000000000000c303c0c303c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_50 : relabelI rowB_137 (nat_lit 0x1c303c0c303c0000000000000000000c303c0c303c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_51 : relabelI rowB_17 (nat_lit 0x1c303c0c303c0000000000000000000c303c1c303c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_52 : relabelI rowB_245 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_53 : relabelI rowB_484 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_54 : relabelI rowB_251 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_55 : relabelI rowB_11 (nat_lit 0x3c0c3800203800000000000000000008002c00f32c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_56 : relabelI rowB_256 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_57 : relabelI rowB_490 (nat_lit 0xc3c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_58 : relabelI rowB_149 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_59 : relabelI rowB_196 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_60 : relabelI rowB_269 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_61 : relabelI rowB_508 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_62 : relabelI rowB_293 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_63 : relabelI rowB_155 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_64 : relabelI rowB_275 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_65 : relabelI rowB_35 (nat_lit 0xc3d30000000000000000004d00000000b2000000000000000000cbc300000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_66 : relabelI rowB_299 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_67 : relabelI rowB_1 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_68 : relabelI rowB_25 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_69 : relabelI rowB_31 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_70 : relabelI rowB_3 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_71 : relabelI rowB_13 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_72 : relabelI rowB_27 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_73 : relabelI rowB_73 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_74 : relabelI rowB_33 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_75 : relabelI rowB_37 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_76 : relabelI rowB_79 (nat_lit 0xc3c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_77 : relabelI rowB_39 (nat_lit 0xcf0030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_78 : relabelI rowB_18 (nat_lit 0x20383c0c3800000000000000000000000000000000000000000000000000c3d3040013000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_79 : relabelI rowB_121 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_80 : relabelI rowB_241 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_81 : relabelI rowB_23 (nat_lit 0x8002c00f32c000000000000000000000000000000000000000000000000cf00320000b2000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_82 : relabelI rowB_123 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_83 : relabelI rowB_5 (nat_lit 0xc00f30c00f30000000000000000000c00f30c01f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_84 : relabelI rowB_11 (nat_lit 0xc00f30c00f30000000000000000000c00f34c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_85 : relabelI rowB_125 (nat_lit 0xc00f30c00f30000000000000000000c01f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_86 : relabelI rowB_131 (nat_lit 0xc00f30c00f30000000000000000004c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_87 : relabelI rowB_3 (nat_lit 0xc00f30c01f30000000000000000000c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_88 : relabelI rowB_5 (nat_lit 0xc00f30c01f30000000000000000000c01f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_89 : relabelI rowB_9 (nat_lit 0xc00f34c00f30000000000000000000c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_90 : relabelI rowB_5 (nat_lit 0xc00f34c00f30000000000000000000c01f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_91 : relabelI rowB_11 (nat_lit 0xc00f34c00f30000000000000000004c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_92 : relabelI rowB_123 (nat_lit 0xc01f30c00f30000000000000000000c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_93 : relabelI rowB_3 (nat_lit 0xc01f30c00f30000000000000000000c00f30c01f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_94 : relabelI rowB_3 (nat_lit 0xc01f30c00f30000000000000000000c00f34c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_95 : relabelI rowB_133 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_96 : relabelI rowB_19 (nat_lit 0xc303c0c303c0000000000000000000000000000000000000000000000000c00f30c01f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_97 : relabelI rowB_21 (nat_lit 0xc303c0c303c0000000000000000000000000000000000000000000000000c00f34c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_98 : relabelI rowB_139 (nat_lit 0xc303c0c303c0000000000000000000000000000000000000000000000000c01f30c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_99 : relabelI rowB_141 (nat_lit 0xc303c0c303c0000000000000000000000000000000000000000000000004c00f30c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_100 : relabelI rowB_15 (nat_lit 0xc303c1c303c0000000000000000000000000000000000000000000000000c00f30c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_101 : relabelI rowB_19 (nat_lit 0xc303c1c303c0000000000000000000000000000000000000000000000000c01f30c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_102 : relabelI rowB_21 (nat_lit 0xc303c1c303c0000000000000000000000000000000000000000000000004c00f30c00f3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_103 : relabelI rowB_243 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_104 : relabelI rowB_481 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_105 : relabelI rowB_249 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_106 : relabelI rowB_9 (nat_lit 0x3c0c3800203800000000000000000000000000000000000000000000000004001300c3d3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_107 : relabelI rowB_129 (nat_lit 0x4c00f30c00f30000000000000000000c00f30c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_108 : relabelI rowB_9 (nat_lit 0x4c00f30c00f30000000000000000000c00f30c01f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_109 : relabelI rowB_9 (nat_lit 0x4c00f30c00f30000000000000000000c00f34c00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_110 : relabelI rowB_147 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_111 : relabelI rowB_193 (nat_lit 0xc303c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_112 : relabelI rowB_267 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_113 : relabelI rowB_505 (nat_lit 0x30cf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_114 : relabelI rowB_291 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_115 : relabelI rowB_11 (nat_lit 0x500000000000000001214001200001700000000000000003a5c003a000012000000000000000028480028000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_116 : relabelI rowB_17 (nat_lit 0x500000000000000001214001200001700000000000000203a5c003a00001200000000000000702c48002c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_117 : relabelI rowB_11 (nat_lit 0x50000000000000001d31400130000170000000000000000ba5c003a000012000000000000000028480028000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_118 : relabelI rowB_9 (nat_lit 0x1700000000000000003a5c003a000005000000000000000012140012000005000000000000000012140012000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_119 : relabelI rowB_9 (nat_lit 0x170000000000000000ba5c003a0000050000000000000001d3140013000005000000000000000012140012000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_120 : relabelI rowB_15 (nat_lit 0x1700000000000000203a5c003a0000050000000000000000121400120000050000000000000001d3140013000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_121 : relabelI rowB_51 (nat_lit 0x2d00000000003a000000b40e80000005000000000012000000140480000000000000000000000000000000000005000000000000000012140012000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_122 : relabelI rowB_57 (nat_lit 0x6d00000000003a000000b40e800004c70000000000120000001c0480000000000000000000000000000000000005000000000000000012140012000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_123 : relabelI rowB_129 (nat_lit 0x5c00000000000005c003a00003a000140000000000000140012000012000140000000000000140012000012000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_124 : relabelI rowB_129 (nat_lit 0x5c00000000000005c003a0000ba0001400000000000001400130001d3000140000000000000140012000012000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_125 : relabelI rowB_135 (nat_lit 0x5c00000000000005c003a00203a0001400000000000001400120000120001400000000000001400130001d3000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_126 : relabelI rowB_153 (nat_lit 0x5d70000000000005c00005c0000000145000000000000140000140000000145000000000000140000140000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_127 : relabelI rowB_153 (nat_lit 0x5d70000000000005c00005c040000014d000000000000140000340e00000145000000000000140000140000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_128 : relabelI rowB_159 (nat_lit 0x5d70000000000005c00005d000000014500000000000014000014000000014d000000000000140000340e00000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_129 : relabelI rowB_273 (nat_lit 0x5d70000000000005c04005c0000000345000000000000340e00140000000145000000000000140000140000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_130 : relabelI rowB_155 (nat_lit 0x5d70000000000005c04005d0000000345000000000000340c0014000000014d000000000000140000340e00000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_131 : relabelI rowB_285 (nat_lit 0x5d70000000000005c04005d0000000345000000000000340e0014000000014d000000000000140000340c00000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_132 : relabelI rowB_33 (nat_lit 0x101700000000000000003a5c003a01300d000000000000000012340012000005000000000000000012140012000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_133 : relabelI rowB_9 (nat_lit 0x300d00000000000000001234001200101700000000000000203a5c003a00001200000000000000702c48002c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_134 : relabelI rowB_153 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_135 : relabelI rowB_35 (nat_lit 0x30cf0000000000000000003c0c300030cf0000000000000000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_136 : relabelI rowB_59 (nat_lit 0x30cf0000000000000000003c0c300030cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_137 : relabelI rowB_155 (nat_lit 0x30cf0000000000000000003c0c300034cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_138 : relabelI rowB_33 (nat_lit 0x30cf0000000000000000003c0c380030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_139 : relabelI rowB_35 (nat_lit 0x30cf0000000000000000003c0c380034cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_140 : relabelI rowB_57 (nat_lit 0x30cf0000000000000000003c0e300030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_141 : relabelI rowB_35 (nat_lit 0x30cf0000000000000000003c0e300034cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_142 : relabelI rowB_153 (nat_lit 0x34cf0000000000000000003c0c300030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_143 : relabelI rowB_33 (nat_lit 0x34cf0000000000000000003c0c300030cf0000000000000000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_144 : relabelI rowB_33 (nat_lit 0x34cf0000000000000000003c0c300030cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_145 : relabelI rowB_249 (nat_lit 0x34cf0000000000004d000000000000000000000000000000000000000000034100000000000034cf00000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_146 : relabelI rowB_297 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_147 : relabelI rowB_293 (nat_lit 0xf30c0000003c0c3000000000000000f30c0000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_148 : relabelI rowB_413 (nat_lit 0xf30c0000003c0c3000000000000000f30c0000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_149 : relabelI rowB_299 (nat_lit 0xf30c0000003c0c3000000000000000f32c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_150 : relabelI rowB_291 (nat_lit 0xf30c0000003c0c3800000000000000f30c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_151 : relabelI rowB_293 (nat_lit 0xf30c0000003c0c3800000000000000f32c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_152 : relabelI rowB_411 (nat_lit 0xf30c0000003c0e3000000000000000f30c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_153 : relabelI rowB_293 (nat_lit 0xf30c0000003c0e3000000000000000f32c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_154 : relabelI rowB_417 (nat_lit 0xfb0c0000003c0c3000000000000000f30c0000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_155 : relabelI rowB_299 (nat_lit 0xfb0c0000003c0c3000000000000000f30c0000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_156 : relabelI rowB_411 (nat_lit 0xfb0c0000003c0c3000000000000000f30c0000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_157 : relabelI rowB_35 (nat_lit 0x1300d00000000000000001234001200101700000000000000003a5c003a000012000000000000000028480028000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_158 : relabelI rowB_47 (nat_lit 0x1300d00000000000000001234001200101700000000000000203a5c003a00001200000000000000302c48002c000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_159 : relabelI rowB_0 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_160 : relabelI rowB_24 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_161 : relabelI rowB_30 (nat_lit 0xf30c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_162 : relabelI rowB_2 (nat_lit 0xc00f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_163 : relabelI rowB_26 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_164 : relabelI rowB_32 (nat_lit 0x3c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_165 : relabelI rowB_36 (nat_lit 0xc3300c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_166 : relabelI rowB_3 (nat_lit 0x4dc3300d000000000000000000300cc7001007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_167 : relabelI rowB_120 (nat_lit 0x30cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_168 : relabelI rowB_1 (nat_lit 0x30cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_169 : relabelI rowB_7 (nat_lit 0x30cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_170 : relabelI rowB_121 (nat_lit 0x30cf0030cf0000000000000000000034cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_171 : relabelI rowB_127 (nat_lit 0x30cf0030cf0000000000000000000130cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_172 : relabelI rowB_0 (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_173 : relabelI rowB_1 (nat_lit 0x30cf0034cf0000000000000000000034cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_174 : relabelI rowB_7 (nat_lit 0x30cf0034cf0000000000000000000130cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_175 : relabelI rowB_6 (nat_lit 0x30cf0130cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_176 : relabelI rowB_1 (nat_lit 0x30cf0130cf0000000000000000000034cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_177 : relabelI rowB_7 (nat_lit 0x30cf0130cf0000000000000000000130cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_178 : relabelI rowB_120 (nat_lit 0x34cf0030cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := by
  decide +kernel

theorem excWit_179 : relabelI rowB_0 (nat_lit 0x34cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := by
  decide +kernel

theorem excWit_180 : relabelI rowB_0 (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := by
  decide +kernel

theorem excWit_181 : relabelI rowB_240 (nat_lit 0xc3c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 9 0 := by
  decide +kernel

theorem excWit_182 : relabelI rowB_22 (nat_lit 0x8002c00f32c000000000000000000000000000000000000000000000000000000000000000000000000000000c3300d00004d000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := by
  decide +kernel

theorem excWit_183 : relabelI rowB_1 (nat_lit 0x50000050001450000000000000000170000170005d7000000000000000012000012000492000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_184 : relabelI rowB_3 (nat_lit 0x50000050001450000000000000000170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_185 : relabelI rowB_1 (nat_lit 0x501300d00014d0000000000000000170010170005d7000000000000000012000012000492000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_186 : relabelI rowB_5 (nat_lit 0x501300d00014d0000000000000400170010170005d70000000000000c0032000012000c92000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_187 : relabelI rowB_4 (nat_lit 0x120000120004920000000000000000120000120004920000000000000000170000170005d7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_188 : relabelI rowB_5 (nat_lit 0x120000120004920000000000000000124c00320004b20000000000000000170400170005d7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_189 : relabelI rowB_0 (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_190 : relabelI rowB_0 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_191 : relabelI rowB_2 (nat_lit 0x170400170005d700000000000000000500000500014500000000000000000501300d00014d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_192 : relabelI rowB_145 (nat_lit 0x1450001400001400000000000000005d70005c00005c0000000000000000492000480000480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_193 : relabelI rowB_147 (nat_lit 0x1450001400001400000000000000005d70005c01005c00000000000000004b2000480b00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_194 : relabelI rowB_144 (nat_lit 0x34500c3400001400000000000000005d70045c01005c00000000000000004b2000480b00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_195 : relabelI rowB_124 (nat_lit 0x4800004920000120000000000000004800004920000120000000000000005c00005d7000017000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_196 : relabelI rowB_125 (nat_lit 0x4800004920000120000000000000004800004b24c00320000000000000005c00005d7040017000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_197 : relabelI rowB_148 (nat_lit 0x4920004800004800000000000000004920004800004800000000000000005d70005c00005c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_198 : relabelI rowB_269 (nat_lit 0x492000480000480000000000000000c92b00c800004800000000000000005d71005c00005c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_199 : relabelI rowB_144 (nat_lit 0x5d70005c00005c0000000000000000145000140000140000000000000000145000140000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := by
  decide +kernel

theorem excWit_200 : relabelI rowB_146 (nat_lit 0x5d70005c01005c000000000000000014500014000014000000000000000014d00014002c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_201 : relabelI rowB_264 (nat_lit 0x5d70045c00005c000000000000000034502c340000140000000000000000145000140000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := by
  decide +kernel

theorem excWit_202 : relabelI rowB_145 (nat_lit 0x5d70045c01005c000000000000000034500c34000014000000000000000014d00014002c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem excWit_203 : relabelI rowB_268 (nat_lit 0x5d70045c01005c000000000000000034502c34000014000000000000000014d00014000c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := by
  decide +kernel

theorem exc6_keys : exc6.keysC = exc6keys := by
  decide +kernel

end CDCert.K6
