/-
CDCert.K6.Check5 — kernel-checked identification of the generated five-level data
(`CDCert.K6.Data5`) with their definitions:

* `groups4_eq`: `groups4` are the pre-shifted masks over `lexOrders 4` of `groupsEP 4`;
* `groups5n_eq`: `groups5n` are the pre-shifted masks over `lexOrders 5` of `groupsPF5`;
* `lifts5_eq`: `lifts5` lists, for each four-order, the mask over `lexOrders 5` of the
  five-orders whose deletion of label 4 is that order;
* `rows4_eq`, `rows5_eq`: the relabelling rows are `lexIdx (rlab σ L)` over
  `lexOrders`;
* `lexIdx_lexOrders4/5`: `lexIdx` is the position in `lexOrders 4/5`;
* `rep4T_eq`, `rep5T_eq`: the representative trees list `reps4`, `reps5` in order.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex5
import CDCert.K6.Defs5
import CDCert.K6.Data5
import CDCert.K6.Data6
import CDCert.K6.Check6
import CDCert.Bitset

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000
set_option Elab.async false

/-- Pre-shifted mask over `lexOrders 4`. -/
def shiftMask4 (o : Opt (List Nat)) : Nat := maskOf (lexOrders 4) o <<< 64

/-- Pre-shifted mask over `lexOrders 5`. -/
def shiftMask5 (o : Opt (List Nat)) : Nat := maskOf (lexOrders 5) o <<< 64

theorem g4_0_eq : g4_0 = (pairOptions 0 1).map shiftMask4 := by decide +kernel

theorem g4_1_eq : g4_1 = (lawsExtreme.map (holdsL 0 1 2)).map shiftMask4 := by decide +kernel

theorem g4_2_eq : g4_2 = (pairOptions 0 2).map shiftMask4 := by decide +kernel

theorem g4_3_eq : g4_3 = (pairOptions 1 2).map shiftMask4 := by decide +kernel

theorem g4_4_eq : g4_4 = (lawsExtreme.map (holdsL 0 1 3)).map shiftMask4 := by decide +kernel

theorem g4_5_eq : g4_5 = (lawsExtreme.map (holdsL 0 2 3)).map shiftMask4 := by decide +kernel

theorem g4_6_eq : g4_6 = (lawsExtreme.map (holdsL 1 2 3)).map shiftMask4 := by decide +kernel

theorem g4_7_eq : g4_7 = (pairOptions 0 3).map shiftMask4 := by decide +kernel

theorem g4_8_eq : g4_8 = (pairOptions 1 3).map shiftMask4 := by decide +kernel

theorem g4_9_eq : g4_9 = (pairOptions 2 3).map shiftMask4 := by decide +kernel

theorem lexOrders4_eq : lexOrders 4 = [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]] := by
  decide +kernel

theorem groups4_eq : groups4 = (groupsEP 4).map (fun g => g.map shiftMask4) := by
  show [g4_0, g4_1, g4_2, g4_3, g4_4, g4_5, g4_6, g4_7, g4_8, g4_9] = _
  rw [g4_0_eq, g4_1_eq, g4_2_eq, g4_3_eq, g4_4_eq, g4_5_eq, g4_6_eq, g4_7_eq, g4_8_eq, g4_9_eq]
  rfl

theorem g5n_0_eq : g5n_0 = (pairOptions 0 4).map shiftMask5 := by decide +kernel

theorem g5n_1_eq : g5n_1 = (pairOptions 1 4).map shiftMask5 := by decide +kernel

theorem g5n_2_eq : g5n_2 = (pairOptions 2 4).map shiftMask5 := by decide +kernel

theorem g5n_3_eq : g5n_3 = (pairOptions 3 4).map shiftMask5 := by decide +kernel

theorem g5n_4_eq : g5n_4 = (lawsExtreme.map (holdsL 0 1 4)).map shiftMask5 := by decide +kernel

theorem g5n_5_eq : g5n_5 = (lawsExtreme.map (holdsL 0 2 4)).map shiftMask5 := by decide +kernel

theorem g5n_6_eq : g5n_6 = (lawsExtreme.map (holdsL 0 3 4)).map shiftMask5 := by decide +kernel

theorem g5n_7_eq : g5n_7 = (lawsExtreme.map (holdsL 1 2 4)).map shiftMask5 := by decide +kernel

theorem g5n_8_eq : g5n_8 = (lawsExtreme.map (holdsL 1 3 4)).map shiftMask5 := by decide +kernel

theorem g5n_9_eq : g5n_9 = (lawsExtreme.map (holdsL 2 3 4)).map shiftMask5 := by decide +kernel

theorem groups5n_eq : groups5n = groupsPF5.map (fun g => g.map shiftMask5) := by
  show [g5n_0, g5n_1, g5n_2, g5n_3, g5n_4, g5n_5, g5n_6, g5n_7, g5n_8, g5n_9] = _
  rw [g5n_0_eq, g5n_1_eq, g5n_2_eq, g5n_3_eq, g5n_4_eq, g5n_5_eq, g5n_6_eq, g5n_7_eq, g5n_8_eq, g5n_9_eq]
  rfl

theorem lifts5_eq : lifts5 = (lexOrders 4).map (fun q => maskOf (lexOrders 5) (fun L => deleteLabel 4 L == q)) := by
  decide +kernel

theorem r4_0_eq : r4_0 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 1, 2, 3] L)) := by decide +kernel

theorem r4_1_eq : r4_1 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 1, 3, 2] L)) := by decide +kernel

theorem r4_2_eq : r4_2 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 2, 1, 3] L)) := by decide +kernel

theorem r4_3_eq : r4_3 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 2, 3, 1] L)) := by decide +kernel

theorem r4_4_eq : r4_4 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 3, 1, 2] L)) := by decide +kernel

theorem r4_5_eq : r4_5 = (lexOrders 4).map (fun L => lexIdx (rlab [0, 3, 2, 1] L)) := by decide +kernel

theorem r4_6_eq : r4_6 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 0, 2, 3] L)) := by decide +kernel

theorem r4_7_eq : r4_7 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 0, 3, 2] L)) := by decide +kernel

theorem r4_8_eq : r4_8 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 2, 0, 3] L)) := by decide +kernel

theorem r4_9_eq : r4_9 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 2, 3, 0] L)) := by decide +kernel

theorem r4_10_eq : r4_10 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 3, 0, 2] L)) := by decide +kernel

theorem r4_11_eq : r4_11 = (lexOrders 4).map (fun L => lexIdx (rlab [1, 3, 2, 0] L)) := by decide +kernel

theorem r4_12_eq : r4_12 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 0, 1, 3] L)) := by decide +kernel

theorem r4_13_eq : r4_13 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 0, 3, 1] L)) := by decide +kernel

theorem r4_14_eq : r4_14 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 1, 0, 3] L)) := by decide +kernel

theorem r4_15_eq : r4_15 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 1, 3, 0] L)) := by decide +kernel

theorem r4_16_eq : r4_16 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 3, 0, 1] L)) := by decide +kernel

theorem r4_17_eq : r4_17 = (lexOrders 4).map (fun L => lexIdx (rlab [2, 3, 1, 0] L)) := by decide +kernel

theorem r4_18_eq : r4_18 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 0, 1, 2] L)) := by decide +kernel

theorem r4_19_eq : r4_19 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 0, 2, 1] L)) := by decide +kernel

theorem r4_20_eq : r4_20 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 1, 0, 2] L)) := by decide +kernel

theorem r4_21_eq : r4_21 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 1, 2, 0] L)) := by decide +kernel

theorem r4_22_eq : r4_22 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 2, 0, 1] L)) := by decide +kernel

theorem r4_23_eq : r4_23 = (lexOrders 4).map (fun L => lexIdx (rlab [3, 2, 1, 0] L)) := by decide +kernel

theorem rows4_eq : rows4 = (lexOrders 4).map (fun σ => (lexOrders 4).map (fun L => lexIdx (rlab σ L))) := by
  show [r4_0, r4_1, r4_2, r4_3, r4_4, r4_5, r4_6, r4_7, r4_8, r4_9, r4_10, r4_11, r4_12, r4_13, r4_14, r4_15, r4_16, r4_17, r4_18, r4_19, r4_20, r4_21, r4_22, r4_23] = _
  rw [r4_0_eq, r4_1_eq, r4_2_eq, r4_3_eq, r4_4_eq, r4_5_eq, r4_6_eq, r4_7_eq, r4_8_eq, r4_9_eq, r4_10_eq, r4_11_eq, r4_12_eq, r4_13_eq, r4_14_eq, r4_15_eq, r4_16_eq, r4_17_eq, r4_18_eq, r4_19_eq, r4_20_eq, r4_21_eq, r4_22_eq, r4_23_eq]
  rw [lexOrders4_eq]
  rfl

theorem r5_0_eq : r5_0 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 2, 3, 4] L)) := by decide +kernel

theorem r5_1_eq : r5_1 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 2, 4, 3] L)) := by decide +kernel

theorem r5_2_eq : r5_2 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 3, 2, 4] L)) := by decide +kernel

theorem r5_3_eq : r5_3 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 3, 4, 2] L)) := by decide +kernel

theorem r5_4_eq : r5_4 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 4, 2, 3] L)) := by decide +kernel

theorem r5_5_eq : r5_5 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 1, 4, 3, 2] L)) := by decide +kernel

theorem r5_6_eq : r5_6 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 1, 3, 4] L)) := by decide +kernel

theorem r5_7_eq : r5_7 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 1, 4, 3] L)) := by decide +kernel

theorem r5_8_eq : r5_8 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 3, 1, 4] L)) := by decide +kernel

theorem r5_9_eq : r5_9 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 3, 4, 1] L)) := by decide +kernel

theorem r5_10_eq : r5_10 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 4, 1, 3] L)) := by decide +kernel

theorem r5_11_eq : r5_11 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 2, 4, 3, 1] L)) := by decide +kernel

theorem r5_12_eq : r5_12 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 1, 2, 4] L)) := by decide +kernel

theorem r5_13_eq : r5_13 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 1, 4, 2] L)) := by decide +kernel

theorem r5_14_eq : r5_14 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 2, 1, 4] L)) := by decide +kernel

theorem r5_15_eq : r5_15 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 2, 4, 1] L)) := by decide +kernel

theorem r5_16_eq : r5_16 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 4, 1, 2] L)) := by decide +kernel

theorem r5_17_eq : r5_17 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 3, 4, 2, 1] L)) := by decide +kernel

theorem r5_18_eq : r5_18 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 1, 2, 3] L)) := by decide +kernel

theorem r5_19_eq : r5_19 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 1, 3, 2] L)) := by decide +kernel

theorem r5_20_eq : r5_20 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 2, 1, 3] L)) := by decide +kernel

theorem r5_21_eq : r5_21 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 2, 3, 1] L)) := by decide +kernel

theorem r5_22_eq : r5_22 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 3, 1, 2] L)) := by decide +kernel

theorem r5_23_eq : r5_23 = (lexOrders 5).map (fun L => lexIdx (rlab [0, 4, 3, 2, 1] L)) := by decide +kernel

theorem r5_24_eq : r5_24 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 2, 3, 4] L)) := by decide +kernel

theorem r5_25_eq : r5_25 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 2, 4, 3] L)) := by decide +kernel

theorem r5_26_eq : r5_26 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 3, 2, 4] L)) := by decide +kernel

theorem r5_27_eq : r5_27 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 3, 4, 2] L)) := by decide +kernel

theorem r5_28_eq : r5_28 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 4, 2, 3] L)) := by decide +kernel

theorem r5_29_eq : r5_29 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 0, 4, 3, 2] L)) := by decide +kernel

theorem r5_30_eq : r5_30 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 0, 3, 4] L)) := by decide +kernel

theorem r5_31_eq : r5_31 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 0, 4, 3] L)) := by decide +kernel

theorem r5_32_eq : r5_32 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 3, 0, 4] L)) := by decide +kernel

theorem r5_33_eq : r5_33 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 3, 4, 0] L)) := by decide +kernel

theorem r5_34_eq : r5_34 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 4, 0, 3] L)) := by decide +kernel

theorem r5_35_eq : r5_35 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 2, 4, 3, 0] L)) := by decide +kernel

theorem r5_36_eq : r5_36 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 0, 2, 4] L)) := by decide +kernel

theorem r5_37_eq : r5_37 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 0, 4, 2] L)) := by decide +kernel

theorem r5_38_eq : r5_38 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 2, 0, 4] L)) := by decide +kernel

theorem r5_39_eq : r5_39 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 2, 4, 0] L)) := by decide +kernel

theorem r5_40_eq : r5_40 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 4, 0, 2] L)) := by decide +kernel

theorem r5_41_eq : r5_41 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 3, 4, 2, 0] L)) := by decide +kernel

theorem r5_42_eq : r5_42 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 0, 2, 3] L)) := by decide +kernel

theorem r5_43_eq : r5_43 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 0, 3, 2] L)) := by decide +kernel

theorem r5_44_eq : r5_44 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 2, 0, 3] L)) := by decide +kernel

theorem r5_45_eq : r5_45 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 2, 3, 0] L)) := by decide +kernel

theorem r5_46_eq : r5_46 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 3, 0, 2] L)) := by decide +kernel

theorem r5_47_eq : r5_47 = (lexOrders 5).map (fun L => lexIdx (rlab [1, 4, 3, 2, 0] L)) := by decide +kernel

theorem r5_48_eq : r5_48 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 1, 3, 4] L)) := by decide +kernel

theorem r5_49_eq : r5_49 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 1, 4, 3] L)) := by decide +kernel

theorem r5_50_eq : r5_50 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 3, 1, 4] L)) := by decide +kernel

theorem r5_51_eq : r5_51 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 3, 4, 1] L)) := by decide +kernel

theorem r5_52_eq : r5_52 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 4, 1, 3] L)) := by decide +kernel

theorem r5_53_eq : r5_53 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 0, 4, 3, 1] L)) := by decide +kernel

theorem r5_54_eq : r5_54 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 0, 3, 4] L)) := by decide +kernel

theorem r5_55_eq : r5_55 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 0, 4, 3] L)) := by decide +kernel

theorem r5_56_eq : r5_56 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 3, 0, 4] L)) := by decide +kernel

theorem r5_57_eq : r5_57 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 3, 4, 0] L)) := by decide +kernel

theorem r5_58_eq : r5_58 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 4, 0, 3] L)) := by decide +kernel

theorem r5_59_eq : r5_59 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 1, 4, 3, 0] L)) := by decide +kernel

theorem r5_60_eq : r5_60 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 0, 1, 4] L)) := by decide +kernel

theorem r5_61_eq : r5_61 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 0, 4, 1] L)) := by decide +kernel

theorem r5_62_eq : r5_62 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 1, 0, 4] L)) := by decide +kernel

theorem r5_63_eq : r5_63 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 1, 4, 0] L)) := by decide +kernel

theorem r5_64_eq : r5_64 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 4, 0, 1] L)) := by decide +kernel

theorem r5_65_eq : r5_65 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 3, 4, 1, 0] L)) := by decide +kernel

theorem r5_66_eq : r5_66 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 0, 1, 3] L)) := by decide +kernel

theorem r5_67_eq : r5_67 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 0, 3, 1] L)) := by decide +kernel

theorem r5_68_eq : r5_68 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 1, 0, 3] L)) := by decide +kernel

theorem r5_69_eq : r5_69 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 1, 3, 0] L)) := by decide +kernel

theorem r5_70_eq : r5_70 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 3, 0, 1] L)) := by decide +kernel

theorem r5_71_eq : r5_71 = (lexOrders 5).map (fun L => lexIdx (rlab [2, 4, 3, 1, 0] L)) := by decide +kernel

theorem r5_72_eq : r5_72 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 1, 2, 4] L)) := by decide +kernel

theorem r5_73_eq : r5_73 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 1, 4, 2] L)) := by decide +kernel

theorem r5_74_eq : r5_74 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 2, 1, 4] L)) := by decide +kernel

theorem r5_75_eq : r5_75 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 2, 4, 1] L)) := by decide +kernel

theorem r5_76_eq : r5_76 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 4, 1, 2] L)) := by decide +kernel

theorem r5_77_eq : r5_77 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 0, 4, 2, 1] L)) := by decide +kernel

theorem r5_78_eq : r5_78 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 0, 2, 4] L)) := by decide +kernel

theorem r5_79_eq : r5_79 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 0, 4, 2] L)) := by decide +kernel

theorem r5_80_eq : r5_80 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 2, 0, 4] L)) := by decide +kernel

theorem r5_81_eq : r5_81 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 2, 4, 0] L)) := by decide +kernel

theorem r5_82_eq : r5_82 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 4, 0, 2] L)) := by decide +kernel

theorem r5_83_eq : r5_83 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 1, 4, 2, 0] L)) := by decide +kernel

theorem r5_84_eq : r5_84 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 0, 1, 4] L)) := by decide +kernel

theorem r5_85_eq : r5_85 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 0, 4, 1] L)) := by decide +kernel

theorem r5_86_eq : r5_86 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 1, 0, 4] L)) := by decide +kernel

theorem r5_87_eq : r5_87 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 1, 4, 0] L)) := by decide +kernel

theorem r5_88_eq : r5_88 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 4, 0, 1] L)) := by decide +kernel

theorem r5_89_eq : r5_89 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 2, 4, 1, 0] L)) := by decide +kernel

theorem r5_90_eq : r5_90 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 0, 1, 2] L)) := by decide +kernel

theorem r5_91_eq : r5_91 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 0, 2, 1] L)) := by decide +kernel

theorem r5_92_eq : r5_92 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 1, 0, 2] L)) := by decide +kernel

theorem r5_93_eq : r5_93 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 1, 2, 0] L)) := by decide +kernel

theorem r5_94_eq : r5_94 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 2, 0, 1] L)) := by decide +kernel

theorem r5_95_eq : r5_95 = (lexOrders 5).map (fun L => lexIdx (rlab [3, 4, 2, 1, 0] L)) := by decide +kernel

theorem r5_96_eq : r5_96 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 1, 2, 3] L)) := by decide +kernel

theorem r5_97_eq : r5_97 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 1, 3, 2] L)) := by decide +kernel

theorem r5_98_eq : r5_98 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 2, 1, 3] L)) := by decide +kernel

theorem r5_99_eq : r5_99 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 2, 3, 1] L)) := by decide +kernel

theorem r5_100_eq : r5_100 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 3, 1, 2] L)) := by decide +kernel

theorem r5_101_eq : r5_101 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 0, 3, 2, 1] L)) := by decide +kernel

theorem r5_102_eq : r5_102 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 0, 2, 3] L)) := by decide +kernel

theorem r5_103_eq : r5_103 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 0, 3, 2] L)) := by decide +kernel

theorem r5_104_eq : r5_104 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 2, 0, 3] L)) := by decide +kernel

theorem r5_105_eq : r5_105 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 2, 3, 0] L)) := by decide +kernel

theorem r5_106_eq : r5_106 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 3, 0, 2] L)) := by decide +kernel

theorem r5_107_eq : r5_107 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 1, 3, 2, 0] L)) := by decide +kernel

theorem r5_108_eq : r5_108 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 0, 1, 3] L)) := by decide +kernel

theorem r5_109_eq : r5_109 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 0, 3, 1] L)) := by decide +kernel

theorem r5_110_eq : r5_110 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 1, 0, 3] L)) := by decide +kernel

theorem r5_111_eq : r5_111 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 1, 3, 0] L)) := by decide +kernel

theorem r5_112_eq : r5_112 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 3, 0, 1] L)) := by decide +kernel

theorem r5_113_eq : r5_113 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 2, 3, 1, 0] L)) := by decide +kernel

theorem r5_114_eq : r5_114 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 0, 1, 2] L)) := by decide +kernel

theorem r5_115_eq : r5_115 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 0, 2, 1] L)) := by decide +kernel

theorem r5_116_eq : r5_116 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 1, 0, 2] L)) := by decide +kernel

theorem r5_117_eq : r5_117 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 1, 2, 0] L)) := by decide +kernel

theorem r5_118_eq : r5_118 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 2, 0, 1] L)) := by decide +kernel

theorem r5_119_eq : r5_119 = (lexOrders 5).map (fun L => lexIdx (rlab [4, 3, 2, 1, 0] L)) := by decide +kernel

theorem rows5_eq : rows5 = (lexOrders 5).map (fun σ => (lexOrders 5).map (fun L => lexIdx (rlab σ L))) := by
  show [r5_0, r5_1, r5_2, r5_3, r5_4, r5_5, r5_6, r5_7, r5_8, r5_9, r5_10, r5_11, r5_12, r5_13, r5_14, r5_15, r5_16, r5_17, r5_18, r5_19, r5_20, r5_21, r5_22, r5_23, r5_24, r5_25, r5_26, r5_27, r5_28, r5_29, r5_30, r5_31, r5_32, r5_33, r5_34, r5_35, r5_36, r5_37, r5_38, r5_39, r5_40, r5_41, r5_42, r5_43, r5_44, r5_45, r5_46, r5_47, r5_48, r5_49, r5_50, r5_51, r5_52, r5_53, r5_54, r5_55, r5_56, r5_57, r5_58, r5_59, r5_60, r5_61, r5_62, r5_63, r5_64, r5_65, r5_66, r5_67, r5_68, r5_69, r5_70, r5_71, r5_72, r5_73, r5_74, r5_75, r5_76, r5_77, r5_78, r5_79, r5_80, r5_81, r5_82, r5_83, r5_84, r5_85, r5_86, r5_87, r5_88, r5_89, r5_90, r5_91, r5_92, r5_93, r5_94, r5_95, r5_96, r5_97, r5_98, r5_99, r5_100, r5_101, r5_102, r5_103, r5_104, r5_105, r5_106, r5_107, r5_108, r5_109, r5_110, r5_111, r5_112, r5_113, r5_114, r5_115, r5_116, r5_117, r5_118, r5_119] = _
  rw [r5_0_eq, r5_1_eq, r5_2_eq, r5_3_eq, r5_4_eq, r5_5_eq, r5_6_eq, r5_7_eq, r5_8_eq, r5_9_eq, r5_10_eq, r5_11_eq, r5_12_eq, r5_13_eq, r5_14_eq, r5_15_eq, r5_16_eq, r5_17_eq, r5_18_eq, r5_19_eq, r5_20_eq, r5_21_eq, r5_22_eq, r5_23_eq, r5_24_eq, r5_25_eq, r5_26_eq, r5_27_eq, r5_28_eq, r5_29_eq, r5_30_eq, r5_31_eq, r5_32_eq, r5_33_eq, r5_34_eq, r5_35_eq, r5_36_eq, r5_37_eq, r5_38_eq, r5_39_eq, r5_40_eq, r5_41_eq, r5_42_eq, r5_43_eq, r5_44_eq, r5_45_eq, r5_46_eq, r5_47_eq, r5_48_eq, r5_49_eq, r5_50_eq, r5_51_eq, r5_52_eq, r5_53_eq, r5_54_eq, r5_55_eq, r5_56_eq, r5_57_eq, r5_58_eq, r5_59_eq, r5_60_eq, r5_61_eq, r5_62_eq, r5_63_eq, r5_64_eq, r5_65_eq, r5_66_eq, r5_67_eq, r5_68_eq, r5_69_eq, r5_70_eq, r5_71_eq, r5_72_eq, r5_73_eq, r5_74_eq, r5_75_eq, r5_76_eq, r5_77_eq, r5_78_eq, r5_79_eq, r5_80_eq, r5_81_eq, r5_82_eq, r5_83_eq, r5_84_eq, r5_85_eq, r5_86_eq, r5_87_eq, r5_88_eq, r5_89_eq, r5_90_eq, r5_91_eq, r5_92_eq, r5_93_eq, r5_94_eq, r5_95_eq, r5_96_eq, r5_97_eq, r5_98_eq, r5_99_eq, r5_100_eq, r5_101_eq, r5_102_eq, r5_103_eq, r5_104_eq, r5_105_eq, r5_106_eq, r5_107_eq, r5_108_eq, r5_109_eq, r5_110_eq, r5_111_eq, r5_112_eq, r5_113_eq, r5_114_eq, r5_115_eq, r5_116_eq, r5_117_eq, r5_118_eq, r5_119_eq]
  rw [lexOrders5_eq]
  rfl

theorem lexIdx_lexOrders4 : (lexOrders 4).map lexIdx = List.range 24 := by decide +kernel

theorem lexIdx_lexOrders5 : (lexOrders 5).map lexIdx = List.range 120 := by decide +kernel

theorem rep4T_eq : (List.range 45).map rep4T.find = reps4 := by decide +kernel

theorem rep5T_eq : (List.range 1160).map rep5T.find = reps5 := by decide +kernel

end CDCert.K6
