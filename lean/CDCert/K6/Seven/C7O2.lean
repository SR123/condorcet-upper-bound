/-
CDCert.K6.Seven.C7O2 — part of kernel checks of the seven-level option data (option masks, part 2) (Claude's generator
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

theorem oc1_91_eq : oc1_91 = Nat.shiftLeft (maskOfK cm7_0 17222) 64 := by decide +kernel
theorem oc3_91_eq : oc3_91 = Nat.shiftLeft (maskOfK cm7_2 17222) 64 := by decide +kernel
theorem oc1_92_eq : oc1_92 = Nat.shiftLeft (maskOfK cm7_0 2886) 64 := by decide +kernel
theorem oc3_92_eq : oc3_92 = Nat.shiftLeft (maskOfK cm7_2 2886) 64 := by decide +kernel
theorem oc1_93_eq : oc1_93 = Nat.shiftLeft (maskOfK cm7_0 19270) 64 := by decide +kernel
theorem oc3_93_eq : oc3_93 = Nat.shiftLeft (maskOfK cm7_2 19270) 64 := by decide +kernel
theorem oc1_94_eq : oc1_94 = Nat.shiftLeft (maskOfK cm7_0 4934) 64 := by decide +kernel
theorem oc3_94_eq : oc3_94 = Nat.shiftLeft (maskOfK cm7_2 4934) 64 := by decide +kernel
theorem oc1_95_eq : oc1_95 = Nat.shiftLeft (maskOfK cm7_0 21318) 64 := by decide +kernel
theorem oc3_95_eq : oc3_95 = Nat.shiftLeft (maskOfK cm7_2 21318) 64 := by decide +kernel
theorem oc1_96_eq : oc1_96 = Nat.shiftLeft (maskOfK cm7_0 1094) 64 := by decide +kernel
theorem oc3_96_eq : oc3_96 = Nat.shiftLeft (maskOfK cm7_2 1094) 64 := by decide +kernel
theorem oc1_97_eq : oc1_97 = Nat.shiftLeft (maskOfK cm7_0 17478) 64 := by decide +kernel
theorem oc3_97_eq : oc3_97 = Nat.shiftLeft (maskOfK cm7_2 17478) 64 := by decide +kernel
theorem oc1_98_eq : oc1_98 = Nat.shiftLeft (maskOfK cm7_0 3142) 64 := by decide +kernel
theorem oc3_98_eq : oc3_98 = Nat.shiftLeft (maskOfK cm7_2 3142) 64 := by decide +kernel
theorem oc1_99_eq : oc1_99 = Nat.shiftLeft (maskOfK cm7_0 19526) 64 := by decide +kernel
theorem oc3_99_eq : oc3_99 = Nat.shiftLeft (maskOfK cm7_2 19526) 64 := by decide +kernel
theorem oc1_100_eq : oc1_100 = Nat.shiftLeft (maskOfK cm7_0 5190) 64 := by decide +kernel
theorem oc3_100_eq : oc3_100 = Nat.shiftLeft (maskOfK cm7_2 5190) 64 := by decide +kernel
theorem oc1_101_eq : oc1_101 = Nat.shiftLeft (maskOfK cm7_0 21574) 64 := by decide +kernel
theorem oc3_101_eq : oc3_101 = Nat.shiftLeft (maskOfK cm7_2 21574) 64 := by decide +kernel
theorem oc1_102_eq : oc1_102 = Nat.shiftLeft (maskOfK cm7_0 1350) 64 := by decide +kernel
theorem oc3_102_eq : oc3_102 = Nat.shiftLeft (maskOfK cm7_2 1350) 64 := by decide +kernel
theorem oc1_103_eq : oc1_103 = Nat.shiftLeft (maskOfK cm7_0 17734) 64 := by decide +kernel
theorem oc3_103_eq : oc3_103 = Nat.shiftLeft (maskOfK cm7_2 17734) 64 := by decide +kernel
theorem oc1_104_eq : oc1_104 = Nat.shiftLeft (maskOfK cm7_0 3398) 64 := by decide +kernel
theorem oc3_104_eq : oc3_104 = Nat.shiftLeft (maskOfK cm7_2 3398) 64 := by decide +kernel
theorem oc1_105_eq : oc1_105 = Nat.shiftLeft (maskOfK cm7_0 19782) 64 := by decide +kernel
theorem oc3_105_eq : oc3_105 = Nat.shiftLeft (maskOfK cm7_2 19782) 64 := by decide +kernel
theorem oc1_106_eq : oc1_106 = Nat.shiftLeft (maskOfK cm7_0 5446) 64 := by decide +kernel
theorem oc3_106_eq : oc3_106 = Nat.shiftLeft (maskOfK cm7_2 5446) 64 := by decide +kernel
theorem oc1_107_eq : oc1_107 = Nat.shiftLeft (maskOfK cm7_0 21830) 64 := by decide +kernel
theorem oc3_107_eq : oc3_107 = Nat.shiftLeft (maskOfK cm7_2 21830) 64 := by decide +kernel
theorem oc1_108_eq : oc1_108 = Nat.shiftLeft (maskOfK cm7_0 1606) 64 := by decide +kernel
theorem oc3_108_eq : oc3_108 = Nat.shiftLeft (maskOfK cm7_2 1606) 64 := by decide +kernel
theorem oc1_109_eq : oc1_109 = Nat.shiftLeft (maskOfK cm7_0 17990) 64 := by decide +kernel
theorem oc3_109_eq : oc3_109 = Nat.shiftLeft (maskOfK cm7_2 17990) 64 := by decide +kernel
theorem oc1_110_eq : oc1_110 = Nat.shiftLeft (maskOfK cm7_0 3654) 64 := by decide +kernel
theorem oc3_110_eq : oc3_110 = Nat.shiftLeft (maskOfK cm7_2 3654) 64 := by decide +kernel
theorem oc1_111_eq : oc1_111 = Nat.shiftLeft (maskOfK cm7_0 20038) 64 := by decide +kernel
theorem oc3_111_eq : oc3_111 = Nat.shiftLeft (maskOfK cm7_2 20038) 64 := by decide +kernel
theorem oc1_112_eq : oc1_112 = Nat.shiftLeft (maskOfK cm7_0 5702) 64 := by decide +kernel
theorem oc3_112_eq : oc3_112 = Nat.shiftLeft (maskOfK cm7_2 5702) 64 := by decide +kernel
theorem oc1_113_eq : oc1_113 = Nat.shiftLeft (maskOfK cm7_0 22086) 64 := by decide +kernel
theorem oc3_113_eq : oc3_113 = Nat.shiftLeft (maskOfK cm7_2 22086) 64 := by decide +kernel
theorem oc1_114_eq : oc1_114 = Nat.shiftLeft (maskOfK cm7_0 1126) 64 := by decide +kernel
theorem oc3_114_eq : oc3_114 = Nat.shiftLeft (maskOfK cm7_2 1126) 64 := by decide +kernel
theorem oc1_115_eq : oc1_115 = Nat.shiftLeft (maskOfK cm7_0 17510) 64 := by decide +kernel
theorem oc3_115_eq : oc3_115 = Nat.shiftLeft (maskOfK cm7_2 17510) 64 := by decide +kernel
theorem oc1_116_eq : oc1_116 = Nat.shiftLeft (maskOfK cm7_0 3174) 64 := by decide +kernel
theorem oc3_116_eq : oc3_116 = Nat.shiftLeft (maskOfK cm7_2 3174) 64 := by decide +kernel
theorem oc1_117_eq : oc1_117 = Nat.shiftLeft (maskOfK cm7_0 19558) 64 := by decide +kernel
theorem oc3_117_eq : oc3_117 = Nat.shiftLeft (maskOfK cm7_2 19558) 64 := by decide +kernel
theorem oc1_118_eq : oc1_118 = Nat.shiftLeft (maskOfK cm7_0 5222) 64 := by decide +kernel
theorem oc3_118_eq : oc3_118 = Nat.shiftLeft (maskOfK cm7_2 5222) 64 := by decide +kernel
theorem oc1_119_eq : oc1_119 = Nat.shiftLeft (maskOfK cm7_0 21606) 64 := by decide +kernel
theorem oc3_119_eq : oc3_119 = Nat.shiftLeft (maskOfK cm7_2 21606) 64 := by decide +kernel
theorem oc1_120_eq : oc1_120 = Nat.shiftLeft (maskOfK cm7_0 1382) 64 := by decide +kernel
theorem oc3_120_eq : oc3_120 = Nat.shiftLeft (maskOfK cm7_2 1382) 64 := by decide +kernel
theorem oc1_121_eq : oc1_121 = Nat.shiftLeft (maskOfK cm7_0 17766) 64 := by decide +kernel
theorem oc3_121_eq : oc3_121 = Nat.shiftLeft (maskOfK cm7_2 17766) 64 := by decide +kernel
theorem oc1_122_eq : oc1_122 = Nat.shiftLeft (maskOfK cm7_0 3430) 64 := by decide +kernel
theorem oc3_122_eq : oc3_122 = Nat.shiftLeft (maskOfK cm7_2 3430) 64 := by decide +kernel
theorem oc1_123_eq : oc1_123 = Nat.shiftLeft (maskOfK cm7_0 19814) 64 := by decide +kernel
theorem oc3_123_eq : oc3_123 = Nat.shiftLeft (maskOfK cm7_2 19814) 64 := by decide +kernel
theorem oc1_124_eq : oc1_124 = Nat.shiftLeft (maskOfK cm7_0 5478) 64 := by decide +kernel
theorem oc3_124_eq : oc3_124 = Nat.shiftLeft (maskOfK cm7_2 5478) 64 := by decide +kernel
theorem oc1_125_eq : oc1_125 = Nat.shiftLeft (maskOfK cm7_0 21862) 64 := by decide +kernel
theorem oc3_125_eq : oc3_125 = Nat.shiftLeft (maskOfK cm7_2 21862) 64 := by decide +kernel
theorem oc1_126_eq : oc1_126 = Nat.shiftLeft (maskOfK cm7_0 1638) 64 := by decide +kernel
theorem oc3_126_eq : oc3_126 = Nat.shiftLeft (maskOfK cm7_2 1638) 64 := by decide +kernel
theorem oc1_127_eq : oc1_127 = Nat.shiftLeft (maskOfK cm7_0 18022) 64 := by decide +kernel
theorem oc3_127_eq : oc3_127 = Nat.shiftLeft (maskOfK cm7_2 18022) 64 := by decide +kernel
theorem oc1_128_eq : oc1_128 = Nat.shiftLeft (maskOfK cm7_0 3686) 64 := by decide +kernel
theorem oc3_128_eq : oc3_128 = Nat.shiftLeft (maskOfK cm7_2 3686) 64 := by decide +kernel
theorem oc1_129_eq : oc1_129 = Nat.shiftLeft (maskOfK cm7_0 20070) 64 := by decide +kernel
theorem oc3_129_eq : oc3_129 = Nat.shiftLeft (maskOfK cm7_2 20070) 64 := by decide +kernel
theorem oc1_130_eq : oc1_130 = Nat.shiftLeft (maskOfK cm7_0 5734) 64 := by decide +kernel
theorem oc3_130_eq : oc3_130 = Nat.shiftLeft (maskOfK cm7_2 5734) 64 := by decide +kernel
theorem oc1_131_eq : oc1_131 = Nat.shiftLeft (maskOfK cm7_0 22118) 64 := by decide +kernel
theorem oc3_131_eq : oc3_131 = Nat.shiftLeft (maskOfK cm7_2 22118) 64 := by decide +kernel
theorem oc1_132_eq : oc1_132 = Nat.shiftLeft (maskOfK cm7_0 1414) 64 := by decide +kernel
theorem oc3_132_eq : oc3_132 = Nat.shiftLeft (maskOfK cm7_2 1414) 64 := by decide +kernel
theorem oc1_133_eq : oc1_133 = Nat.shiftLeft (maskOfK cm7_0 17798) 64 := by decide +kernel
theorem oc3_133_eq : oc3_133 = Nat.shiftLeft (maskOfK cm7_2 17798) 64 := by decide +kernel
theorem oc1_134_eq : oc1_134 = Nat.shiftLeft (maskOfK cm7_0 3462) 64 := by decide +kernel
theorem oc3_134_eq : oc3_134 = Nat.shiftLeft (maskOfK cm7_2 3462) 64 := by decide +kernel
theorem oc1_135_eq : oc1_135 = Nat.shiftLeft (maskOfK cm7_0 19846) 64 := by decide +kernel
theorem oc3_135_eq : oc3_135 = Nat.shiftLeft (maskOfK cm7_2 19846) 64 := by decide +kernel
theorem oc1_136_eq : oc1_136 = Nat.shiftLeft (maskOfK cm7_0 5510) 64 := by decide +kernel
end CDCert.K6
