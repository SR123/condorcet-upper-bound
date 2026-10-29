/-
CDCert.K6.Check6 — kernel-checked identification of the generated six-level data
(`CDCert.K6.Data6`) with their definitions:

* `groups6_eq`: the literal option masks `groups6` are exactly the pre-shifted
  masks over `base12` of the list-level options `groupsPF6`;
* `lexOrders5_eq`: the 120 five-orders in lexicographic order, explicitly;
* `lifts6_eq`: `lifts6` lists, for each five-order of `lexOrders 5`, the mask over
  `base12` of the six-orders whose deletion of label 5 is that order.

Each entry is checked by the kernel in its own theorem (bounded memory).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Lex
import CDCert.K6.Data6
import CDCert.Bitset

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option maxRecDepth 100000
set_option Elab.async false

/-- The pre-shifted mask map. -/
def shiftMask (o : Opt (List Nat)) : Nat := maskOf base12 o <<< 64

theorem g6_0_eq : g6_0 = (pairOptions 0 5).map shiftMask := by decide +kernel

theorem g6_1_eq : g6_1 = (pairOptions 1 5).map shiftMask := by decide +kernel

theorem g6_2_eq : g6_2 = (pairOptions 2 5).map shiftMask := by decide +kernel

theorem g6_3_eq : g6_3 = (pairOptions 3 5).map shiftMask := by decide +kernel

theorem g6_4_eq : g6_4 = (pairOptions 4 5).map shiftMask := by decide +kernel

theorem g6_5_eq : g6_5 = (lawsExtreme.map (holdsL 0 1 5)).map shiftMask := by
  decide +kernel

theorem g6_6_eq : g6_6 = (lawsExtreme.map (holdsL 0 2 5)).map shiftMask := by
  decide +kernel

theorem g6_7_eq : g6_7 = (lawsExtreme.map (holdsL 0 3 5)).map shiftMask := by
  decide +kernel

theorem g6_8_eq : g6_8 = (lawsExtreme.map (holdsL 0 4 5)).map shiftMask := by
  decide +kernel

theorem g6_9_eq : g6_9 = (lawsExtreme.map (holdsL 1 2 5)).map shiftMask := by
  decide +kernel

theorem g6_10_eq : g6_10 = (lawsExtreme.map (holdsL 1 3 5)).map shiftMask := by
  decide +kernel

theorem g6_11_eq : g6_11 = (lawsExtreme.map (holdsL 1 4 5)).map shiftMask := by
  decide +kernel

theorem g6_12_eq : g6_12 = (lawsExtreme.map (holdsL 2 3 5)).map shiftMask := by
  decide +kernel

theorem g6_13_eq : g6_13 = (lawsExtreme.map (holdsL 2 4 5)).map shiftMask := by
  decide +kernel

theorem g6_14_eq : g6_14 = (lawsExtreme.map (holdsL 3 4 5)).map shiftMask := by
  decide +kernel

theorem groups6_eq : groups6 = groupsPF6.map (fun g => g.map shiftMask) := by
  show [g6_0, g6_1, g6_2, g6_3, g6_4, g6_5, g6_6, g6_7, g6_8, g6_9, g6_10, g6_11, g6_12, g6_13, g6_14] = _
  rw [g6_0_eq, g6_1_eq, g6_2_eq, g6_3_eq, g6_4_eq, g6_5_eq, g6_6_eq, g6_7_eq, g6_8_eq, g6_9_eq, g6_10_eq, g6_11_eq, g6_12_eq, g6_13_eq, g6_14_eq]
  rfl

theorem lexOrders5_eq : lexOrders 5 = [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 1, 3, 2, 4], [0, 1, 3, 4, 2], [0, 1, 4, 2, 3], [0, 1, 4, 3, 2], [0, 2, 1, 3, 4], [0, 2, 1, 4, 3], [0, 2, 3, 1, 4], [0, 2, 3, 4, 1], [0, 2, 4, 1, 3], [0, 2, 4, 3, 1], [0, 3, 1, 2, 4], [0, 3, 1, 4, 2], [0, 3, 2, 1, 4], [0, 3, 2, 4, 1], [0, 3, 4, 1, 2], [0, 3, 4, 2, 1], [0, 4, 1, 2, 3], [0, 4, 1, 3, 2], [0, 4, 2, 1, 3], [0, 4, 2, 3, 1], [0, 4, 3, 1, 2], [0, 4, 3, 2, 1], [1, 0, 2, 3, 4], [1, 0, 2, 4, 3], [1, 0, 3, 2, 4], [1, 0, 3, 4, 2], [1, 0, 4, 2, 3], [1, 0, 4, 3, 2], [1, 2, 0, 3, 4], [1, 2, 0, 4, 3], [1, 2, 3, 0, 4], [1, 2, 3, 4, 0], [1, 2, 4, 0, 3], [1, 2, 4, 3, 0], [1, 3, 0, 2, 4], [1, 3, 0, 4, 2], [1, 3, 2, 0, 4], [1, 3, 2, 4, 0], [1, 3, 4, 0, 2], [1, 3, 4, 2, 0], [1, 4, 0, 2, 3], [1, 4, 0, 3, 2], [1, 4, 2, 0, 3], [1, 4, 2, 3, 0], [1, 4, 3, 0, 2], [1, 4, 3, 2, 0], [2, 0, 1, 3, 4], [2, 0, 1, 4, 3], [2, 0, 3, 1, 4], [2, 0, 3, 4, 1], [2, 0, 4, 1, 3], [2, 0, 4, 3, 1], [2, 1, 0, 3, 4], [2, 1, 0, 4, 3], [2, 1, 3, 0, 4], [2, 1, 3, 4, 0], [2, 1, 4, 0, 3], [2, 1, 4, 3, 0], [2, 3, 0, 1, 4], [2, 3, 0, 4, 1], [2, 3, 1, 0, 4], [2, 3, 1, 4, 0], [2, 3, 4, 0, 1], [2, 3, 4, 1, 0], [2, 4, 0, 1, 3], [2, 4, 0, 3, 1], [2, 4, 1, 0, 3], [2, 4, 1, 3, 0], [2, 4, 3, 0, 1], [2, 4, 3, 1, 0], [3, 0, 1, 2, 4], [3, 0, 1, 4, 2], [3, 0, 2, 1, 4], [3, 0, 2, 4, 1], [3, 0, 4, 1, 2], [3, 0, 4, 2, 1], [3, 1, 0, 2, 4], [3, 1, 0, 4, 2], [3, 1, 2, 0, 4], [3, 1, 2, 4, 0], [3, 1, 4, 0, 2], [3, 1, 4, 2, 0], [3, 2, 0, 1, 4], [3, 2, 0, 4, 1], [3, 2, 1, 0, 4], [3, 2, 1, 4, 0], [3, 2, 4, 0, 1], [3, 2, 4, 1, 0], [3, 4, 0, 1, 2], [3, 4, 0, 2, 1], [3, 4, 1, 0, 2], [3, 4, 1, 2, 0], [3, 4, 2, 0, 1], [3, 4, 2, 1, 0], [4, 0, 1, 2, 3], [4, 0, 1, 3, 2], [4, 0, 2, 1, 3], [4, 0, 2, 3, 1], [4, 0, 3, 1, 2], [4, 0, 3, 2, 1], [4, 1, 0, 2, 3], [4, 1, 0, 3, 2], [4, 1, 2, 0, 3], [4, 1, 2, 3, 0], [4, 1, 3, 0, 2], [4, 1, 3, 2, 0], [4, 2, 0, 1, 3], [4, 2, 0, 3, 1], [4, 2, 1, 0, 3], [4, 2, 1, 3, 0], [4, 2, 3, 0, 1], [4, 2, 3, 1, 0], [4, 3, 0, 1, 2], [4, 3, 0, 2, 1], [4, 3, 1, 0, 2], [4, 3, 1, 2, 0], [4, 3, 2, 0, 1], [4, 3, 2, 1, 0]] := by
  decide +kernel

theorem l6_0_eq : l6_0 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 2, 3, 4]) := by
  decide +kernel

theorem l6_1_eq : l6_1 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 2, 4, 3]) := by
  decide +kernel

theorem l6_2_eq : l6_2 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 3, 2, 4]) := by
  decide +kernel

theorem l6_3_eq : l6_3 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 3, 4, 2]) := by
  decide +kernel

theorem l6_4_eq : l6_4 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 4, 2, 3]) := by
  decide +kernel

theorem l6_5_eq : l6_5 = maskOf base12 (fun L => deleteLabel 5 L == [0, 1, 4, 3, 2]) := by
  decide +kernel

theorem l6_6_eq : l6_6 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 1, 3, 4]) := by
  decide +kernel

theorem l6_7_eq : l6_7 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 1, 4, 3]) := by
  decide +kernel

theorem l6_8_eq : l6_8 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 3, 1, 4]) := by
  decide +kernel

theorem l6_9_eq : l6_9 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 3, 4, 1]) := by
  decide +kernel

theorem l6_10_eq : l6_10 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 4, 1, 3]) := by
  decide +kernel

theorem l6_11_eq : l6_11 = maskOf base12 (fun L => deleteLabel 5 L == [0, 2, 4, 3, 1]) := by
  decide +kernel

theorem l6_12_eq : l6_12 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 1, 2, 4]) := by
  decide +kernel

theorem l6_13_eq : l6_13 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 1, 4, 2]) := by
  decide +kernel

theorem l6_14_eq : l6_14 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 2, 1, 4]) := by
  decide +kernel

theorem l6_15_eq : l6_15 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 2, 4, 1]) := by
  decide +kernel

theorem l6_16_eq : l6_16 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 4, 1, 2]) := by
  decide +kernel

theorem l6_17_eq : l6_17 = maskOf base12 (fun L => deleteLabel 5 L == [0, 3, 4, 2, 1]) := by
  decide +kernel

theorem l6_18_eq : l6_18 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 1, 2, 3]) := by
  decide +kernel

theorem l6_19_eq : l6_19 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 1, 3, 2]) := by
  decide +kernel

theorem l6_20_eq : l6_20 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 2, 1, 3]) := by
  decide +kernel

theorem l6_21_eq : l6_21 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 2, 3, 1]) := by
  decide +kernel

theorem l6_22_eq : l6_22 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 3, 1, 2]) := by
  decide +kernel

theorem l6_23_eq : l6_23 = maskOf base12 (fun L => deleteLabel 5 L == [0, 4, 3, 2, 1]) := by
  decide +kernel

theorem l6_24_eq : l6_24 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 2, 3, 4]) := by
  decide +kernel

theorem l6_25_eq : l6_25 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 2, 4, 3]) := by
  decide +kernel

theorem l6_26_eq : l6_26 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 3, 2, 4]) := by
  decide +kernel

theorem l6_27_eq : l6_27 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 3, 4, 2]) := by
  decide +kernel

theorem l6_28_eq : l6_28 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 4, 2, 3]) := by
  decide +kernel

theorem l6_29_eq : l6_29 = maskOf base12 (fun L => deleteLabel 5 L == [1, 0, 4, 3, 2]) := by
  decide +kernel

theorem l6_30_eq : l6_30 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 0, 3, 4]) := by
  decide +kernel

theorem l6_31_eq : l6_31 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 0, 4, 3]) := by
  decide +kernel

theorem l6_32_eq : l6_32 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 3, 0, 4]) := by
  decide +kernel

theorem l6_33_eq : l6_33 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 3, 4, 0]) := by
  decide +kernel

theorem l6_34_eq : l6_34 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 4, 0, 3]) := by
  decide +kernel

theorem l6_35_eq : l6_35 = maskOf base12 (fun L => deleteLabel 5 L == [1, 2, 4, 3, 0]) := by
  decide +kernel

theorem l6_36_eq : l6_36 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 0, 2, 4]) := by
  decide +kernel

theorem l6_37_eq : l6_37 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 0, 4, 2]) := by
  decide +kernel

theorem l6_38_eq : l6_38 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 2, 0, 4]) := by
  decide +kernel

theorem l6_39_eq : l6_39 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 2, 4, 0]) := by
  decide +kernel

theorem l6_40_eq : l6_40 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 4, 0, 2]) := by
  decide +kernel

theorem l6_41_eq : l6_41 = maskOf base12 (fun L => deleteLabel 5 L == [1, 3, 4, 2, 0]) := by
  decide +kernel

theorem l6_42_eq : l6_42 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 0, 2, 3]) := by
  decide +kernel

theorem l6_43_eq : l6_43 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 0, 3, 2]) := by
  decide +kernel

theorem l6_44_eq : l6_44 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 2, 0, 3]) := by
  decide +kernel

theorem l6_45_eq : l6_45 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 2, 3, 0]) := by
  decide +kernel

theorem l6_46_eq : l6_46 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 3, 0, 2]) := by
  decide +kernel

theorem l6_47_eq : l6_47 = maskOf base12 (fun L => deleteLabel 5 L == [1, 4, 3, 2, 0]) := by
  decide +kernel

theorem l6_48_eq : l6_48 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 1, 3, 4]) := by
  decide +kernel

theorem l6_49_eq : l6_49 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 1, 4, 3]) := by
  decide +kernel

theorem l6_50_eq : l6_50 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 3, 1, 4]) := by
  decide +kernel

theorem l6_51_eq : l6_51 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 3, 4, 1]) := by
  decide +kernel

theorem l6_52_eq : l6_52 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 4, 1, 3]) := by
  decide +kernel

theorem l6_53_eq : l6_53 = maskOf base12 (fun L => deleteLabel 5 L == [2, 0, 4, 3, 1]) := by
  decide +kernel

theorem l6_54_eq : l6_54 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 0, 3, 4]) := by
  decide +kernel

theorem l6_55_eq : l6_55 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 0, 4, 3]) := by
  decide +kernel

theorem l6_56_eq : l6_56 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 3, 0, 4]) := by
  decide +kernel

theorem l6_57_eq : l6_57 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 3, 4, 0]) := by
  decide +kernel

theorem l6_58_eq : l6_58 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 4, 0, 3]) := by
  decide +kernel

theorem l6_59_eq : l6_59 = maskOf base12 (fun L => deleteLabel 5 L == [2, 1, 4, 3, 0]) := by
  decide +kernel

theorem l6_60_eq : l6_60 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 0, 1, 4]) := by
  decide +kernel

theorem l6_61_eq : l6_61 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 0, 4, 1]) := by
  decide +kernel

theorem l6_62_eq : l6_62 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 1, 0, 4]) := by
  decide +kernel

theorem l6_63_eq : l6_63 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 1, 4, 0]) := by
  decide +kernel

theorem l6_64_eq : l6_64 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 4, 0, 1]) := by
  decide +kernel

theorem l6_65_eq : l6_65 = maskOf base12 (fun L => deleteLabel 5 L == [2, 3, 4, 1, 0]) := by
  decide +kernel

theorem l6_66_eq : l6_66 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 0, 1, 3]) := by
  decide +kernel

theorem l6_67_eq : l6_67 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 0, 3, 1]) := by
  decide +kernel

theorem l6_68_eq : l6_68 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 1, 0, 3]) := by
  decide +kernel

theorem l6_69_eq : l6_69 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 1, 3, 0]) := by
  decide +kernel

theorem l6_70_eq : l6_70 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 3, 0, 1]) := by
  decide +kernel

theorem l6_71_eq : l6_71 = maskOf base12 (fun L => deleteLabel 5 L == [2, 4, 3, 1, 0]) := by
  decide +kernel

theorem l6_72_eq : l6_72 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 1, 2, 4]) := by
  decide +kernel

theorem l6_73_eq : l6_73 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 1, 4, 2]) := by
  decide +kernel

theorem l6_74_eq : l6_74 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 2, 1, 4]) := by
  decide +kernel

theorem l6_75_eq : l6_75 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 2, 4, 1]) := by
  decide +kernel

theorem l6_76_eq : l6_76 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 4, 1, 2]) := by
  decide +kernel

theorem l6_77_eq : l6_77 = maskOf base12 (fun L => deleteLabel 5 L == [3, 0, 4, 2, 1]) := by
  decide +kernel

theorem l6_78_eq : l6_78 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 0, 2, 4]) := by
  decide +kernel

theorem l6_79_eq : l6_79 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 0, 4, 2]) := by
  decide +kernel

theorem l6_80_eq : l6_80 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 2, 0, 4]) := by
  decide +kernel

theorem l6_81_eq : l6_81 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 2, 4, 0]) := by
  decide +kernel

theorem l6_82_eq : l6_82 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 4, 0, 2]) := by
  decide +kernel

theorem l6_83_eq : l6_83 = maskOf base12 (fun L => deleteLabel 5 L == [3, 1, 4, 2, 0]) := by
  decide +kernel

theorem l6_84_eq : l6_84 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 0, 1, 4]) := by
  decide +kernel

theorem l6_85_eq : l6_85 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 0, 4, 1]) := by
  decide +kernel

theorem l6_86_eq : l6_86 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 1, 0, 4]) := by
  decide +kernel

theorem l6_87_eq : l6_87 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 1, 4, 0]) := by
  decide +kernel

theorem l6_88_eq : l6_88 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 4, 0, 1]) := by
  decide +kernel

theorem l6_89_eq : l6_89 = maskOf base12 (fun L => deleteLabel 5 L == [3, 2, 4, 1, 0]) := by
  decide +kernel

theorem l6_90_eq : l6_90 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 0, 1, 2]) := by
  decide +kernel

theorem l6_91_eq : l6_91 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 0, 2, 1]) := by
  decide +kernel

theorem l6_92_eq : l6_92 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 1, 0, 2]) := by
  decide +kernel

theorem l6_93_eq : l6_93 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 1, 2, 0]) := by
  decide +kernel

theorem l6_94_eq : l6_94 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 2, 0, 1]) := by
  decide +kernel

theorem l6_95_eq : l6_95 = maskOf base12 (fun L => deleteLabel 5 L == [3, 4, 2, 1, 0]) := by
  decide +kernel

theorem l6_96_eq : l6_96 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 1, 2, 3]) := by
  decide +kernel

theorem l6_97_eq : l6_97 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 1, 3, 2]) := by
  decide +kernel

theorem l6_98_eq : l6_98 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 2, 1, 3]) := by
  decide +kernel

theorem l6_99_eq : l6_99 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 2, 3, 1]) := by
  decide +kernel

theorem l6_100_eq : l6_100 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 3, 1, 2]) := by
  decide +kernel

theorem l6_101_eq : l6_101 = maskOf base12 (fun L => deleteLabel 5 L == [4, 0, 3, 2, 1]) := by
  decide +kernel

theorem l6_102_eq : l6_102 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 0, 2, 3]) := by
  decide +kernel

theorem l6_103_eq : l6_103 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 0, 3, 2]) := by
  decide +kernel

theorem l6_104_eq : l6_104 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 2, 0, 3]) := by
  decide +kernel

theorem l6_105_eq : l6_105 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 2, 3, 0]) := by
  decide +kernel

theorem l6_106_eq : l6_106 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 3, 0, 2]) := by
  decide +kernel

theorem l6_107_eq : l6_107 = maskOf base12 (fun L => deleteLabel 5 L == [4, 1, 3, 2, 0]) := by
  decide +kernel

theorem l6_108_eq : l6_108 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 0, 1, 3]) := by
  decide +kernel

theorem l6_109_eq : l6_109 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 0, 3, 1]) := by
  decide +kernel

theorem l6_110_eq : l6_110 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 1, 0, 3]) := by
  decide +kernel

theorem l6_111_eq : l6_111 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 1, 3, 0]) := by
  decide +kernel

theorem l6_112_eq : l6_112 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 3, 0, 1]) := by
  decide +kernel

theorem l6_113_eq : l6_113 = maskOf base12 (fun L => deleteLabel 5 L == [4, 2, 3, 1, 0]) := by
  decide +kernel

theorem l6_114_eq : l6_114 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 0, 1, 2]) := by
  decide +kernel

theorem l6_115_eq : l6_115 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 0, 2, 1]) := by
  decide +kernel

theorem l6_116_eq : l6_116 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 1, 0, 2]) := by
  decide +kernel

theorem l6_117_eq : l6_117 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 1, 2, 0]) := by
  decide +kernel

theorem l6_118_eq : l6_118 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 2, 0, 1]) := by
  decide +kernel

theorem l6_119_eq : l6_119 = maskOf base12 (fun L => deleteLabel 5 L == [4, 3, 2, 1, 0]) := by
  decide +kernel

theorem lifts6_eq : lifts6 = (lexOrders 5).map (fun q => maskOf base12 (fun L => deleteLabel 5 L == q)) := by
  rw [lexOrders5_eq]
  show [l6_0, l6_1, l6_2, l6_3, l6_4, l6_5, l6_6, l6_7, l6_8, l6_9, l6_10, l6_11, l6_12, l6_13, l6_14, l6_15, l6_16, l6_17, l6_18, l6_19, l6_20, l6_21, l6_22, l6_23, l6_24, l6_25, l6_26, l6_27, l6_28, l6_29, l6_30, l6_31, l6_32, l6_33, l6_34, l6_35, l6_36, l6_37, l6_38, l6_39, l6_40, l6_41, l6_42, l6_43, l6_44, l6_45, l6_46, l6_47, l6_48, l6_49, l6_50, l6_51, l6_52, l6_53, l6_54, l6_55, l6_56, l6_57, l6_58, l6_59, l6_60, l6_61, l6_62, l6_63, l6_64, l6_65, l6_66, l6_67, l6_68, l6_69, l6_70, l6_71, l6_72, l6_73, l6_74, l6_75, l6_76, l6_77, l6_78, l6_79, l6_80, l6_81, l6_82, l6_83, l6_84, l6_85, l6_86, l6_87, l6_88, l6_89, l6_90, l6_91, l6_92, l6_93, l6_94, l6_95, l6_96, l6_97, l6_98, l6_99, l6_100, l6_101, l6_102, l6_103, l6_104, l6_105, l6_106, l6_107, l6_108, l6_109, l6_110, l6_111, l6_112, l6_113, l6_114, l6_115, l6_116, l6_117, l6_118, l6_119] = _
  rw [l6_0_eq, l6_1_eq, l6_2_eq, l6_3_eq, l6_4_eq, l6_5_eq, l6_6_eq, l6_7_eq, l6_8_eq, l6_9_eq, l6_10_eq, l6_11_eq, l6_12_eq, l6_13_eq, l6_14_eq, l6_15_eq, l6_16_eq, l6_17_eq, l6_18_eq, l6_19_eq, l6_20_eq, l6_21_eq, l6_22_eq, l6_23_eq, l6_24_eq, l6_25_eq, l6_26_eq, l6_27_eq, l6_28_eq, l6_29_eq, l6_30_eq, l6_31_eq, l6_32_eq, l6_33_eq, l6_34_eq, l6_35_eq, l6_36_eq, l6_37_eq, l6_38_eq, l6_39_eq, l6_40_eq, l6_41_eq, l6_42_eq, l6_43_eq, l6_44_eq, l6_45_eq, l6_46_eq, l6_47_eq, l6_48_eq, l6_49_eq, l6_50_eq, l6_51_eq, l6_52_eq, l6_53_eq, l6_54_eq, l6_55_eq, l6_56_eq, l6_57_eq, l6_58_eq, l6_59_eq, l6_60_eq, l6_61_eq, l6_62_eq, l6_63_eq, l6_64_eq, l6_65_eq, l6_66_eq, l6_67_eq, l6_68_eq, l6_69_eq, l6_70_eq, l6_71_eq, l6_72_eq, l6_73_eq, l6_74_eq, l6_75_eq, l6_76_eq, l6_77_eq, l6_78_eq, l6_79_eq, l6_80_eq, l6_81_eq, l6_82_eq, l6_83_eq, l6_84_eq, l6_85_eq, l6_86_eq, l6_87_eq, l6_88_eq, l6_89_eq, l6_90_eq, l6_91_eq, l6_92_eq, l6_93_eq, l6_94_eq, l6_95_eq, l6_96_eq, l6_97_eq, l6_98_eq, l6_99_eq, l6_100_eq, l6_101_eq, l6_102_eq, l6_103_eq, l6_104_eq, l6_105_eq, l6_106_eq, l6_107_eq, l6_108_eq, l6_109_eq, l6_110_eq, l6_111_eq, l6_112_eq, l6_113_eq, l6_114_eq, l6_115_eq, l6_116_eq, l6_117_eq, l6_118_eq, l6_119_eq]
  rfl

end CDCert.K6
