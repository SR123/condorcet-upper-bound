/-
CDCert.K6.Seven.C7O0 — part of kernel checks of the seven-level option data (option masks, part 0) (Claude's generator
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

theorem oc1_0_eq : oc1_0 = Nat.shiftLeft (maskOfK cm7_0 546) 64 := by decide +kernel
theorem oc3_0_eq : oc3_0 = Nat.shiftLeft (maskOfK cm7_2 546) 64 := by decide +kernel
theorem oc1_1_eq : oc1_1 = Nat.shiftLeft (maskOfK cm7_0 16930) 64 := by decide +kernel
theorem oc3_1_eq : oc3_1 = Nat.shiftLeft (maskOfK cm7_2 16930) 64 := by decide +kernel
theorem oc1_2_eq : oc1_2 = Nat.shiftLeft (maskOfK cm7_0 2594) 64 := by decide +kernel
theorem oc3_2_eq : oc3_2 = Nat.shiftLeft (maskOfK cm7_2 2594) 64 := by decide +kernel
theorem oc1_3_eq : oc1_3 = Nat.shiftLeft (maskOfK cm7_0 18978) 64 := by decide +kernel
theorem oc3_3_eq : oc3_3 = Nat.shiftLeft (maskOfK cm7_2 18978) 64 := by decide +kernel
theorem oc1_4_eq : oc1_4 = Nat.shiftLeft (maskOfK cm7_0 4642) 64 := by decide +kernel
theorem oc3_4_eq : oc3_4 = Nat.shiftLeft (maskOfK cm7_2 4642) 64 := by decide +kernel
theorem oc1_5_eq : oc1_5 = Nat.shiftLeft (maskOfK cm7_0 21026) 64 := by decide +kernel
theorem oc3_5_eq : oc3_5 = Nat.shiftLeft (maskOfK cm7_2 21026) 64 := by decide +kernel
theorem oc1_6_eq : oc1_6 = Nat.shiftLeft (maskOfK cm7_0 802) 64 := by decide +kernel
theorem oc3_6_eq : oc3_6 = Nat.shiftLeft (maskOfK cm7_2 802) 64 := by decide +kernel
theorem oc1_7_eq : oc1_7 = Nat.shiftLeft (maskOfK cm7_0 17186) 64 := by decide +kernel
theorem oc3_7_eq : oc3_7 = Nat.shiftLeft (maskOfK cm7_2 17186) 64 := by decide +kernel
theorem oc1_8_eq : oc1_8 = Nat.shiftLeft (maskOfK cm7_0 2850) 64 := by decide +kernel
theorem oc3_8_eq : oc3_8 = Nat.shiftLeft (maskOfK cm7_2 2850) 64 := by decide +kernel
theorem oc1_9_eq : oc1_9 = Nat.shiftLeft (maskOfK cm7_0 19234) 64 := by decide +kernel
theorem oc3_9_eq : oc3_9 = Nat.shiftLeft (maskOfK cm7_2 19234) 64 := by decide +kernel
theorem oc1_10_eq : oc1_10 = Nat.shiftLeft (maskOfK cm7_0 4898) 64 := by decide +kernel
theorem oc3_10_eq : oc3_10 = Nat.shiftLeft (maskOfK cm7_2 4898) 64 := by decide +kernel
theorem oc1_11_eq : oc1_11 = Nat.shiftLeft (maskOfK cm7_0 21282) 64 := by decide +kernel
theorem oc3_11_eq : oc3_11 = Nat.shiftLeft (maskOfK cm7_2 21282) 64 := by decide +kernel
theorem oc1_12_eq : oc1_12 = Nat.shiftLeft (maskOfK cm7_0 1058) 64 := by decide +kernel
theorem oc3_12_eq : oc3_12 = Nat.shiftLeft (maskOfK cm7_2 1058) 64 := by decide +kernel
theorem oc1_13_eq : oc1_13 = Nat.shiftLeft (maskOfK cm7_0 17442) 64 := by decide +kernel
theorem oc3_13_eq : oc3_13 = Nat.shiftLeft (maskOfK cm7_2 17442) 64 := by decide +kernel
theorem oc1_14_eq : oc1_14 = Nat.shiftLeft (maskOfK cm7_0 3106) 64 := by decide +kernel
theorem oc3_14_eq : oc3_14 = Nat.shiftLeft (maskOfK cm7_2 3106) 64 := by decide +kernel
theorem oc1_15_eq : oc1_15 = Nat.shiftLeft (maskOfK cm7_0 19490) 64 := by decide +kernel
theorem oc3_15_eq : oc3_15 = Nat.shiftLeft (maskOfK cm7_2 19490) 64 := by decide +kernel
theorem oc1_16_eq : oc1_16 = Nat.shiftLeft (maskOfK cm7_0 5154) 64 := by decide +kernel
theorem oc3_16_eq : oc3_16 = Nat.shiftLeft (maskOfK cm7_2 5154) 64 := by decide +kernel
theorem oc1_17_eq : oc1_17 = Nat.shiftLeft (maskOfK cm7_0 21538) 64 := by decide +kernel
theorem oc3_17_eq : oc3_17 = Nat.shiftLeft (maskOfK cm7_2 21538) 64 := by decide +kernel
theorem oc1_18_eq : oc1_18 = Nat.shiftLeft (maskOfK cm7_0 1314) 64 := by decide +kernel
theorem oc3_18_eq : oc3_18 = Nat.shiftLeft (maskOfK cm7_2 1314) 64 := by decide +kernel
theorem oc1_19_eq : oc1_19 = Nat.shiftLeft (maskOfK cm7_0 17698) 64 := by decide +kernel
theorem oc3_19_eq : oc3_19 = Nat.shiftLeft (maskOfK cm7_2 17698) 64 := by decide +kernel
theorem oc1_20_eq : oc1_20 = Nat.shiftLeft (maskOfK cm7_0 3362) 64 := by decide +kernel
theorem oc3_20_eq : oc3_20 = Nat.shiftLeft (maskOfK cm7_2 3362) 64 := by decide +kernel
theorem oc1_21_eq : oc1_21 = Nat.shiftLeft (maskOfK cm7_0 19746) 64 := by decide +kernel
theorem oc3_21_eq : oc3_21 = Nat.shiftLeft (maskOfK cm7_2 19746) 64 := by decide +kernel
theorem oc1_22_eq : oc1_22 = Nat.shiftLeft (maskOfK cm7_0 5410) 64 := by decide +kernel
theorem oc3_22_eq : oc3_22 = Nat.shiftLeft (maskOfK cm7_2 5410) 64 := by decide +kernel
theorem oc1_23_eq : oc1_23 = Nat.shiftLeft (maskOfK cm7_0 21794) 64 := by decide +kernel
theorem oc3_23_eq : oc3_23 = Nat.shiftLeft (maskOfK cm7_2 21794) 64 := by decide +kernel
theorem oc1_24_eq : oc1_24 = Nat.shiftLeft (maskOfK cm7_0 1570) 64 := by decide +kernel
theorem oc3_24_eq : oc3_24 = Nat.shiftLeft (maskOfK cm7_2 1570) 64 := by decide +kernel
theorem oc1_25_eq : oc1_25 = Nat.shiftLeft (maskOfK cm7_0 17954) 64 := by decide +kernel
theorem oc3_25_eq : oc3_25 = Nat.shiftLeft (maskOfK cm7_2 17954) 64 := by decide +kernel
theorem oc1_26_eq : oc1_26 = Nat.shiftLeft (maskOfK cm7_0 3618) 64 := by decide +kernel
theorem oc3_26_eq : oc3_26 = Nat.shiftLeft (maskOfK cm7_2 3618) 64 := by decide +kernel
theorem oc1_27_eq : oc1_27 = Nat.shiftLeft (maskOfK cm7_0 20002) 64 := by decide +kernel
theorem oc3_27_eq : oc3_27 = Nat.shiftLeft (maskOfK cm7_2 20002) 64 := by decide +kernel
theorem oc1_28_eq : oc1_28 = Nat.shiftLeft (maskOfK cm7_0 5666) 64 := by decide +kernel
theorem oc3_28_eq : oc3_28 = Nat.shiftLeft (maskOfK cm7_2 5666) 64 := by decide +kernel
theorem oc1_29_eq : oc1_29 = Nat.shiftLeft (maskOfK cm7_0 22050) 64 := by decide +kernel
theorem oc3_29_eq : oc3_29 = Nat.shiftLeft (maskOfK cm7_2 22050) 64 := by decide +kernel
theorem oc1_30_eq : oc1_30 = Nat.shiftLeft (maskOfK cm7_0 834) 64 := by decide +kernel
theorem oc3_30_eq : oc3_30 = Nat.shiftLeft (maskOfK cm7_2 834) 64 := by decide +kernel
theorem oc1_31_eq : oc1_31 = Nat.shiftLeft (maskOfK cm7_0 17218) 64 := by decide +kernel
theorem oc3_31_eq : oc3_31 = Nat.shiftLeft (maskOfK cm7_2 17218) 64 := by decide +kernel
theorem oc1_32_eq : oc1_32 = Nat.shiftLeft (maskOfK cm7_0 2882) 64 := by decide +kernel
theorem oc3_32_eq : oc3_32 = Nat.shiftLeft (maskOfK cm7_2 2882) 64 := by decide +kernel
theorem oc1_33_eq : oc1_33 = Nat.shiftLeft (maskOfK cm7_0 19266) 64 := by decide +kernel
theorem oc3_33_eq : oc3_33 = Nat.shiftLeft (maskOfK cm7_2 19266) 64 := by decide +kernel
theorem oc1_34_eq : oc1_34 = Nat.shiftLeft (maskOfK cm7_0 4930) 64 := by decide +kernel
theorem oc3_34_eq : oc3_34 = Nat.shiftLeft (maskOfK cm7_2 4930) 64 := by decide +kernel
theorem oc1_35_eq : oc1_35 = Nat.shiftLeft (maskOfK cm7_0 21314) 64 := by decide +kernel
theorem oc3_35_eq : oc3_35 = Nat.shiftLeft (maskOfK cm7_2 21314) 64 := by decide +kernel
theorem oc1_36_eq : oc1_36 = Nat.shiftLeft (maskOfK cm7_0 1090) 64 := by decide +kernel
theorem oc3_36_eq : oc3_36 = Nat.shiftLeft (maskOfK cm7_2 1090) 64 := by decide +kernel
theorem oc1_37_eq : oc1_37 = Nat.shiftLeft (maskOfK cm7_0 17474) 64 := by decide +kernel
theorem oc3_37_eq : oc3_37 = Nat.shiftLeft (maskOfK cm7_2 17474) 64 := by decide +kernel
theorem oc1_38_eq : oc1_38 = Nat.shiftLeft (maskOfK cm7_0 3138) 64 := by decide +kernel
theorem oc3_38_eq : oc3_38 = Nat.shiftLeft (maskOfK cm7_2 3138) 64 := by decide +kernel
theorem oc1_39_eq : oc1_39 = Nat.shiftLeft (maskOfK cm7_0 19522) 64 := by decide +kernel
theorem oc3_39_eq : oc3_39 = Nat.shiftLeft (maskOfK cm7_2 19522) 64 := by decide +kernel
theorem oc1_40_eq : oc1_40 = Nat.shiftLeft (maskOfK cm7_0 5186) 64 := by decide +kernel
theorem oc3_40_eq : oc3_40 = Nat.shiftLeft (maskOfK cm7_2 5186) 64 := by decide +kernel
theorem oc1_41_eq : oc1_41 = Nat.shiftLeft (maskOfK cm7_0 21570) 64 := by decide +kernel
theorem oc3_41_eq : oc3_41 = Nat.shiftLeft (maskOfK cm7_2 21570) 64 := by decide +kernel
theorem oc1_42_eq : oc1_42 = Nat.shiftLeft (maskOfK cm7_0 1346) 64 := by decide +kernel
theorem oc3_42_eq : oc3_42 = Nat.shiftLeft (maskOfK cm7_2 1346) 64 := by decide +kernel
theorem oc1_43_eq : oc1_43 = Nat.shiftLeft (maskOfK cm7_0 17730) 64 := by decide +kernel
theorem oc3_43_eq : oc3_43 = Nat.shiftLeft (maskOfK cm7_2 17730) 64 := by decide +kernel
theorem oc1_44_eq : oc1_44 = Nat.shiftLeft (maskOfK cm7_0 3394) 64 := by decide +kernel
theorem oc3_44_eq : oc3_44 = Nat.shiftLeft (maskOfK cm7_2 3394) 64 := by decide +kernel
theorem oc1_45_eq : oc1_45 = Nat.shiftLeft (maskOfK cm7_0 19778) 64 := by decide +kernel
end CDCert.K6
