/-
CDCert.K6.Seven.C7O1 — part of kernel checks of the seven-level option data (option masks, part 1) (Claude's generator
`mkseven2.py`): packed comparisons are `cmpOf` of the orders of `copy1`/`copy3`; every option mask
is `maskOfK` of its code; `idx1`/`idx3` are the positions in `copy1`/`copy3`; the gather rows are
the positions of the orders of the other copies.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.Opts
import CDCert.K6.Lex7
import CDCert.K6.DefsK7
import CDCert.K6.Idx7

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem oc3_45_eq : oc3_45 = Nat.shiftLeft (maskOfK cm7_2 19778) 64 := by decide +kernel
theorem oc1_46_eq : oc1_46 = Nat.shiftLeft (maskOfK cm7_0 5442) 64 := by decide +kernel
theorem oc3_46_eq : oc3_46 = Nat.shiftLeft (maskOfK cm7_2 5442) 64 := by decide +kernel
theorem oc1_47_eq : oc1_47 = Nat.shiftLeft (maskOfK cm7_0 21826) 64 := by decide +kernel
theorem oc3_47_eq : oc3_47 = Nat.shiftLeft (maskOfK cm7_2 21826) 64 := by decide +kernel
theorem oc1_48_eq : oc1_48 = Nat.shiftLeft (maskOfK cm7_0 1602) 64 := by decide +kernel
theorem oc3_48_eq : oc3_48 = Nat.shiftLeft (maskOfK cm7_2 1602) 64 := by decide +kernel
theorem oc1_49_eq : oc1_49 = Nat.shiftLeft (maskOfK cm7_0 17986) 64 := by decide +kernel
theorem oc3_49_eq : oc3_49 = Nat.shiftLeft (maskOfK cm7_2 17986) 64 := by decide +kernel
theorem oc1_50_eq : oc1_50 = Nat.shiftLeft (maskOfK cm7_0 3650) 64 := by decide +kernel
theorem oc3_50_eq : oc3_50 = Nat.shiftLeft (maskOfK cm7_2 3650) 64 := by decide +kernel
theorem oc1_51_eq : oc1_51 = Nat.shiftLeft (maskOfK cm7_0 20034) 64 := by decide +kernel
theorem oc3_51_eq : oc3_51 = Nat.shiftLeft (maskOfK cm7_2 20034) 64 := by decide +kernel
theorem oc1_52_eq : oc1_52 = Nat.shiftLeft (maskOfK cm7_0 5698) 64 := by decide +kernel
theorem oc3_52_eq : oc3_52 = Nat.shiftLeft (maskOfK cm7_2 5698) 64 := by decide +kernel
theorem oc1_53_eq : oc1_53 = Nat.shiftLeft (maskOfK cm7_0 22082) 64 := by decide +kernel
theorem oc3_53_eq : oc3_53 = Nat.shiftLeft (maskOfK cm7_2 22082) 64 := by decide +kernel
theorem oc1_54_eq : oc1_54 = Nat.shiftLeft (maskOfK cm7_0 1122) 64 := by decide +kernel
theorem oc3_54_eq : oc3_54 = Nat.shiftLeft (maskOfK cm7_2 1122) 64 := by decide +kernel
theorem oc1_55_eq : oc1_55 = Nat.shiftLeft (maskOfK cm7_0 17506) 64 := by decide +kernel
theorem oc3_55_eq : oc3_55 = Nat.shiftLeft (maskOfK cm7_2 17506) 64 := by decide +kernel
theorem oc1_56_eq : oc1_56 = Nat.shiftLeft (maskOfK cm7_0 3170) 64 := by decide +kernel
theorem oc3_56_eq : oc3_56 = Nat.shiftLeft (maskOfK cm7_2 3170) 64 := by decide +kernel
theorem oc1_57_eq : oc1_57 = Nat.shiftLeft (maskOfK cm7_0 19554) 64 := by decide +kernel
theorem oc3_57_eq : oc3_57 = Nat.shiftLeft (maskOfK cm7_2 19554) 64 := by decide +kernel
theorem oc1_58_eq : oc1_58 = Nat.shiftLeft (maskOfK cm7_0 5218) 64 := by decide +kernel
theorem oc3_58_eq : oc3_58 = Nat.shiftLeft (maskOfK cm7_2 5218) 64 := by decide +kernel
theorem oc1_59_eq : oc1_59 = Nat.shiftLeft (maskOfK cm7_0 21602) 64 := by decide +kernel
theorem oc3_59_eq : oc3_59 = Nat.shiftLeft (maskOfK cm7_2 21602) 64 := by decide +kernel
theorem oc1_60_eq : oc1_60 = Nat.shiftLeft (maskOfK cm7_0 1378) 64 := by decide +kernel
theorem oc3_60_eq : oc3_60 = Nat.shiftLeft (maskOfK cm7_2 1378) 64 := by decide +kernel
theorem oc1_61_eq : oc1_61 = Nat.shiftLeft (maskOfK cm7_0 17762) 64 := by decide +kernel
theorem oc3_61_eq : oc3_61 = Nat.shiftLeft (maskOfK cm7_2 17762) 64 := by decide +kernel
theorem oc1_62_eq : oc1_62 = Nat.shiftLeft (maskOfK cm7_0 3426) 64 := by decide +kernel
theorem oc3_62_eq : oc3_62 = Nat.shiftLeft (maskOfK cm7_2 3426) 64 := by decide +kernel
theorem oc1_63_eq : oc1_63 = Nat.shiftLeft (maskOfK cm7_0 19810) 64 := by decide +kernel
theorem oc3_63_eq : oc3_63 = Nat.shiftLeft (maskOfK cm7_2 19810) 64 := by decide +kernel
theorem oc1_64_eq : oc1_64 = Nat.shiftLeft (maskOfK cm7_0 5474) 64 := by decide +kernel
theorem oc3_64_eq : oc3_64 = Nat.shiftLeft (maskOfK cm7_2 5474) 64 := by decide +kernel
theorem oc1_65_eq : oc1_65 = Nat.shiftLeft (maskOfK cm7_0 21858) 64 := by decide +kernel
theorem oc3_65_eq : oc3_65 = Nat.shiftLeft (maskOfK cm7_2 21858) 64 := by decide +kernel
theorem oc1_66_eq : oc1_66 = Nat.shiftLeft (maskOfK cm7_0 1634) 64 := by decide +kernel
theorem oc3_66_eq : oc3_66 = Nat.shiftLeft (maskOfK cm7_2 1634) 64 := by decide +kernel
theorem oc1_67_eq : oc1_67 = Nat.shiftLeft (maskOfK cm7_0 18018) 64 := by decide +kernel
theorem oc3_67_eq : oc3_67 = Nat.shiftLeft (maskOfK cm7_2 18018) 64 := by decide +kernel
theorem oc1_68_eq : oc1_68 = Nat.shiftLeft (maskOfK cm7_0 3682) 64 := by decide +kernel
theorem oc3_68_eq : oc3_68 = Nat.shiftLeft (maskOfK cm7_2 3682) 64 := by decide +kernel
theorem oc1_69_eq : oc1_69 = Nat.shiftLeft (maskOfK cm7_0 20066) 64 := by decide +kernel
theorem oc3_69_eq : oc3_69 = Nat.shiftLeft (maskOfK cm7_2 20066) 64 := by decide +kernel
theorem oc1_70_eq : oc1_70 = Nat.shiftLeft (maskOfK cm7_0 5730) 64 := by decide +kernel
theorem oc3_70_eq : oc3_70 = Nat.shiftLeft (maskOfK cm7_2 5730) 64 := by decide +kernel
theorem oc1_71_eq : oc1_71 = Nat.shiftLeft (maskOfK cm7_0 22114) 64 := by decide +kernel
theorem oc3_71_eq : oc3_71 = Nat.shiftLeft (maskOfK cm7_2 22114) 64 := by decide +kernel
theorem oc1_72_eq : oc1_72 = Nat.shiftLeft (maskOfK cm7_0 1410) 64 := by decide +kernel
theorem oc3_72_eq : oc3_72 = Nat.shiftLeft (maskOfK cm7_2 1410) 64 := by decide +kernel
theorem oc1_73_eq : oc1_73 = Nat.shiftLeft (maskOfK cm7_0 17794) 64 := by decide +kernel
theorem oc3_73_eq : oc3_73 = Nat.shiftLeft (maskOfK cm7_2 17794) 64 := by decide +kernel
theorem oc1_74_eq : oc1_74 = Nat.shiftLeft (maskOfK cm7_0 3458) 64 := by decide +kernel
theorem oc3_74_eq : oc3_74 = Nat.shiftLeft (maskOfK cm7_2 3458) 64 := by decide +kernel
theorem oc1_75_eq : oc1_75 = Nat.shiftLeft (maskOfK cm7_0 19842) 64 := by decide +kernel
theorem oc3_75_eq : oc3_75 = Nat.shiftLeft (maskOfK cm7_2 19842) 64 := by decide +kernel
theorem oc1_76_eq : oc1_76 = Nat.shiftLeft (maskOfK cm7_0 5506) 64 := by decide +kernel
theorem oc3_76_eq : oc3_76 = Nat.shiftLeft (maskOfK cm7_2 5506) 64 := by decide +kernel
theorem oc1_77_eq : oc1_77 = Nat.shiftLeft (maskOfK cm7_0 21890) 64 := by decide +kernel
theorem oc3_77_eq : oc3_77 = Nat.shiftLeft (maskOfK cm7_2 21890) 64 := by decide +kernel
theorem oc1_78_eq : oc1_78 = Nat.shiftLeft (maskOfK cm7_0 1666) 64 := by decide +kernel
theorem oc3_78_eq : oc3_78 = Nat.shiftLeft (maskOfK cm7_2 1666) 64 := by decide +kernel
theorem oc1_79_eq : oc1_79 = Nat.shiftLeft (maskOfK cm7_0 18050) 64 := by decide +kernel
theorem oc3_79_eq : oc3_79 = Nat.shiftLeft (maskOfK cm7_2 18050) 64 := by decide +kernel
theorem oc1_80_eq : oc1_80 = Nat.shiftLeft (maskOfK cm7_0 3714) 64 := by decide +kernel
theorem oc3_80_eq : oc3_80 = Nat.shiftLeft (maskOfK cm7_2 3714) 64 := by decide +kernel
theorem oc1_81_eq : oc1_81 = Nat.shiftLeft (maskOfK cm7_0 20098) 64 := by decide +kernel
theorem oc3_81_eq : oc3_81 = Nat.shiftLeft (maskOfK cm7_2 20098) 64 := by decide +kernel
theorem oc1_82_eq : oc1_82 = Nat.shiftLeft (maskOfK cm7_0 5762) 64 := by decide +kernel
theorem oc3_82_eq : oc3_82 = Nat.shiftLeft (maskOfK cm7_2 5762) 64 := by decide +kernel
theorem oc1_83_eq : oc1_83 = Nat.shiftLeft (maskOfK cm7_0 22146) 64 := by decide +kernel
theorem oc3_83_eq : oc3_83 = Nat.shiftLeft (maskOfK cm7_2 22146) 64 := by decide +kernel
theorem oc1_84_eq : oc1_84 = Nat.shiftLeft (maskOfK cm7_0 1698) 64 := by decide +kernel
theorem oc3_84_eq : oc3_84 = Nat.shiftLeft (maskOfK cm7_2 1698) 64 := by decide +kernel
theorem oc1_85_eq : oc1_85 = Nat.shiftLeft (maskOfK cm7_0 18082) 64 := by decide +kernel
theorem oc3_85_eq : oc3_85 = Nat.shiftLeft (maskOfK cm7_2 18082) 64 := by decide +kernel
theorem oc1_86_eq : oc1_86 = Nat.shiftLeft (maskOfK cm7_0 3746) 64 := by decide +kernel
theorem oc3_86_eq : oc3_86 = Nat.shiftLeft (maskOfK cm7_2 3746) 64 := by decide +kernel
theorem oc1_87_eq : oc1_87 = Nat.shiftLeft (maskOfK cm7_0 20130) 64 := by decide +kernel
theorem oc3_87_eq : oc3_87 = Nat.shiftLeft (maskOfK cm7_2 20130) 64 := by decide +kernel
theorem oc1_88_eq : oc1_88 = Nat.shiftLeft (maskOfK cm7_0 5794) 64 := by decide +kernel
theorem oc3_88_eq : oc3_88 = Nat.shiftLeft (maskOfK cm7_2 5794) 64 := by decide +kernel
theorem oc1_89_eq : oc1_89 = Nat.shiftLeft (maskOfK cm7_0 22178) 64 := by decide +kernel
theorem oc3_89_eq : oc3_89 = Nat.shiftLeft (maskOfK cm7_2 22178) 64 := by decide +kernel
theorem oc1_90_eq : oc1_90 = Nat.shiftLeft (maskOfK cm7_0 838) 64 := by decide +kernel
theorem oc3_90_eq : oc3_90 = Nat.shiftLeft (maskOfK cm7_2 838) 64 := by decide +kernel
end CDCert.K6
