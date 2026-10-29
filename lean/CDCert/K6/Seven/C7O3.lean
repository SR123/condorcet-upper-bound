/-
CDCert.K6.Seven.C7O3 — part of kernel checks of the seven-level option data (option masks, part 3) (Claude's generator
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

theorem oc3_136_eq : oc3_136 = Nat.shiftLeft (maskOfK cm7_2 5510) 64 := by decide +kernel
theorem oc1_137_eq : oc1_137 = Nat.shiftLeft (maskOfK cm7_0 21894) 64 := by decide +kernel
theorem oc3_137_eq : oc3_137 = Nat.shiftLeft (maskOfK cm7_2 21894) 64 := by decide +kernel
theorem oc1_138_eq : oc1_138 = Nat.shiftLeft (maskOfK cm7_0 1670) 64 := by decide +kernel
theorem oc3_138_eq : oc3_138 = Nat.shiftLeft (maskOfK cm7_2 1670) 64 := by decide +kernel
theorem oc1_139_eq : oc1_139 = Nat.shiftLeft (maskOfK cm7_0 18054) 64 := by decide +kernel
theorem oc3_139_eq : oc3_139 = Nat.shiftLeft (maskOfK cm7_2 18054) 64 := by decide +kernel
theorem oc1_140_eq : oc1_140 = Nat.shiftLeft (maskOfK cm7_0 3718) 64 := by decide +kernel
theorem oc3_140_eq : oc3_140 = Nat.shiftLeft (maskOfK cm7_2 3718) 64 := by decide +kernel
theorem oc1_141_eq : oc1_141 = Nat.shiftLeft (maskOfK cm7_0 20102) 64 := by decide +kernel
theorem oc3_141_eq : oc3_141 = Nat.shiftLeft (maskOfK cm7_2 20102) 64 := by decide +kernel
theorem oc1_142_eq : oc1_142 = Nat.shiftLeft (maskOfK cm7_0 5766) 64 := by decide +kernel
theorem oc3_142_eq : oc3_142 = Nat.shiftLeft (maskOfK cm7_2 5766) 64 := by decide +kernel
theorem oc1_143_eq : oc1_143 = Nat.shiftLeft (maskOfK cm7_0 22150) 64 := by decide +kernel
theorem oc3_143_eq : oc3_143 = Nat.shiftLeft (maskOfK cm7_2 22150) 64 := by decide +kernel
theorem oc1_144_eq : oc1_144 = Nat.shiftLeft (maskOfK cm7_0 1702) 64 := by decide +kernel
theorem oc3_144_eq : oc3_144 = Nat.shiftLeft (maskOfK cm7_2 1702) 64 := by decide +kernel
theorem oc1_145_eq : oc1_145 = Nat.shiftLeft (maskOfK cm7_0 18086) 64 := by decide +kernel
theorem oc3_145_eq : oc3_145 = Nat.shiftLeft (maskOfK cm7_2 18086) 64 := by decide +kernel
theorem oc1_146_eq : oc1_146 = Nat.shiftLeft (maskOfK cm7_0 3750) 64 := by decide +kernel
theorem oc3_146_eq : oc3_146 = Nat.shiftLeft (maskOfK cm7_2 3750) 64 := by decide +kernel
theorem oc1_147_eq : oc1_147 = Nat.shiftLeft (maskOfK cm7_0 20134) 64 := by decide +kernel
theorem oc3_147_eq : oc3_147 = Nat.shiftLeft (maskOfK cm7_2 20134) 64 := by decide +kernel
theorem oc1_148_eq : oc1_148 = Nat.shiftLeft (maskOfK cm7_0 5798) 64 := by decide +kernel
theorem oc3_148_eq : oc3_148 = Nat.shiftLeft (maskOfK cm7_2 5798) 64 := by decide +kernel
theorem oc1_149_eq : oc1_149 = Nat.shiftLeft (maskOfK cm7_0 22182) 64 := by decide +kernel
theorem oc3_149_eq : oc3_149 = Nat.shiftLeft (maskOfK cm7_2 22182) 64 := by decide +kernel
theorem oc1_150_eq : oc1_150 = Nat.shiftLeft (maskOfK cm7_0 1130) 64 := by decide +kernel
theorem oc3_150_eq : oc3_150 = Nat.shiftLeft (maskOfK cm7_2 1130) 64 := by decide +kernel
theorem oc1_151_eq : oc1_151 = Nat.shiftLeft (maskOfK cm7_0 17514) 64 := by decide +kernel
theorem oc3_151_eq : oc3_151 = Nat.shiftLeft (maskOfK cm7_2 17514) 64 := by decide +kernel
theorem oc1_152_eq : oc1_152 = Nat.shiftLeft (maskOfK cm7_0 3178) 64 := by decide +kernel
theorem oc3_152_eq : oc3_152 = Nat.shiftLeft (maskOfK cm7_2 3178) 64 := by decide +kernel
theorem oc1_153_eq : oc1_153 = Nat.shiftLeft (maskOfK cm7_0 19562) 64 := by decide +kernel
theorem oc3_153_eq : oc3_153 = Nat.shiftLeft (maskOfK cm7_2 19562) 64 := by decide +kernel
theorem oc1_154_eq : oc1_154 = Nat.shiftLeft (maskOfK cm7_0 5226) 64 := by decide +kernel
theorem oc3_154_eq : oc3_154 = Nat.shiftLeft (maskOfK cm7_2 5226) 64 := by decide +kernel
theorem oc1_155_eq : oc1_155 = Nat.shiftLeft (maskOfK cm7_0 21610) 64 := by decide +kernel
theorem oc3_155_eq : oc3_155 = Nat.shiftLeft (maskOfK cm7_2 21610) 64 := by decide +kernel
theorem oc1_156_eq : oc1_156 = Nat.shiftLeft (maskOfK cm7_0 1386) 64 := by decide +kernel
theorem oc3_156_eq : oc3_156 = Nat.shiftLeft (maskOfK cm7_2 1386) 64 := by decide +kernel
theorem oc1_157_eq : oc1_157 = Nat.shiftLeft (maskOfK cm7_0 17770) 64 := by decide +kernel
theorem oc3_157_eq : oc3_157 = Nat.shiftLeft (maskOfK cm7_2 17770) 64 := by decide +kernel
theorem oc1_158_eq : oc1_158 = Nat.shiftLeft (maskOfK cm7_0 3434) 64 := by decide +kernel
theorem oc3_158_eq : oc3_158 = Nat.shiftLeft (maskOfK cm7_2 3434) 64 := by decide +kernel
theorem oc1_159_eq : oc1_159 = Nat.shiftLeft (maskOfK cm7_0 19818) 64 := by decide +kernel
theorem oc3_159_eq : oc3_159 = Nat.shiftLeft (maskOfK cm7_2 19818) 64 := by decide +kernel
theorem oc1_160_eq : oc1_160 = Nat.shiftLeft (maskOfK cm7_0 5482) 64 := by decide +kernel
theorem oc3_160_eq : oc3_160 = Nat.shiftLeft (maskOfK cm7_2 5482) 64 := by decide +kernel
theorem oc1_161_eq : oc1_161 = Nat.shiftLeft (maskOfK cm7_0 21866) 64 := by decide +kernel
theorem oc3_161_eq : oc3_161 = Nat.shiftLeft (maskOfK cm7_2 21866) 64 := by decide +kernel
theorem oc1_162_eq : oc1_162 = Nat.shiftLeft (maskOfK cm7_0 1642) 64 := by decide +kernel
theorem oc3_162_eq : oc3_162 = Nat.shiftLeft (maskOfK cm7_2 1642) 64 := by decide +kernel
theorem oc1_163_eq : oc1_163 = Nat.shiftLeft (maskOfK cm7_0 18026) 64 := by decide +kernel
theorem oc3_163_eq : oc3_163 = Nat.shiftLeft (maskOfK cm7_2 18026) 64 := by decide +kernel
theorem oc1_164_eq : oc1_164 = Nat.shiftLeft (maskOfK cm7_0 3690) 64 := by decide +kernel
theorem oc3_164_eq : oc3_164 = Nat.shiftLeft (maskOfK cm7_2 3690) 64 := by decide +kernel
theorem oc1_165_eq : oc1_165 = Nat.shiftLeft (maskOfK cm7_0 20074) 64 := by decide +kernel
theorem oc3_165_eq : oc3_165 = Nat.shiftLeft (maskOfK cm7_2 20074) 64 := by decide +kernel
theorem oc1_166_eq : oc1_166 = Nat.shiftLeft (maskOfK cm7_0 5738) 64 := by decide +kernel
theorem oc3_166_eq : oc3_166 = Nat.shiftLeft (maskOfK cm7_2 5738) 64 := by decide +kernel
theorem oc1_167_eq : oc1_167 = Nat.shiftLeft (maskOfK cm7_0 22122) 64 := by decide +kernel
theorem oc3_167_eq : oc3_167 = Nat.shiftLeft (maskOfK cm7_2 22122) 64 := by decide +kernel
theorem oc1_168_eq : oc1_168 = Nat.shiftLeft (maskOfK cm7_0 1418) 64 := by decide +kernel
theorem oc3_168_eq : oc3_168 = Nat.shiftLeft (maskOfK cm7_2 1418) 64 := by decide +kernel
theorem oc1_169_eq : oc1_169 = Nat.shiftLeft (maskOfK cm7_0 17802) 64 := by decide +kernel
theorem oc3_169_eq : oc3_169 = Nat.shiftLeft (maskOfK cm7_2 17802) 64 := by decide +kernel
theorem oc1_170_eq : oc1_170 = Nat.shiftLeft (maskOfK cm7_0 3466) 64 := by decide +kernel
theorem oc3_170_eq : oc3_170 = Nat.shiftLeft (maskOfK cm7_2 3466) 64 := by decide +kernel
theorem oc1_171_eq : oc1_171 = Nat.shiftLeft (maskOfK cm7_0 19850) 64 := by decide +kernel
theorem oc3_171_eq : oc3_171 = Nat.shiftLeft (maskOfK cm7_2 19850) 64 := by decide +kernel
theorem oc1_172_eq : oc1_172 = Nat.shiftLeft (maskOfK cm7_0 5514) 64 := by decide +kernel
theorem oc3_172_eq : oc3_172 = Nat.shiftLeft (maskOfK cm7_2 5514) 64 := by decide +kernel
theorem oc1_173_eq : oc1_173 = Nat.shiftLeft (maskOfK cm7_0 21898) 64 := by decide +kernel
theorem oc3_173_eq : oc3_173 = Nat.shiftLeft (maskOfK cm7_2 21898) 64 := by decide +kernel
theorem oc1_174_eq : oc1_174 = Nat.shiftLeft (maskOfK cm7_0 1674) 64 := by decide +kernel
theorem oc3_174_eq : oc3_174 = Nat.shiftLeft (maskOfK cm7_2 1674) 64 := by decide +kernel
theorem oc1_175_eq : oc1_175 = Nat.shiftLeft (maskOfK cm7_0 18058) 64 := by decide +kernel
theorem oc3_175_eq : oc3_175 = Nat.shiftLeft (maskOfK cm7_2 18058) 64 := by decide +kernel
theorem oc1_176_eq : oc1_176 = Nat.shiftLeft (maskOfK cm7_0 3722) 64 := by decide +kernel
theorem oc3_176_eq : oc3_176 = Nat.shiftLeft (maskOfK cm7_2 3722) 64 := by decide +kernel
theorem oc1_177_eq : oc1_177 = Nat.shiftLeft (maskOfK cm7_0 20106) 64 := by decide +kernel
theorem oc3_177_eq : oc3_177 = Nat.shiftLeft (maskOfK cm7_2 20106) 64 := by decide +kernel
theorem oc1_178_eq : oc1_178 = Nat.shiftLeft (maskOfK cm7_0 5770) 64 := by decide +kernel
theorem oc3_178_eq : oc3_178 = Nat.shiftLeft (maskOfK cm7_2 5770) 64 := by decide +kernel
theorem oc1_179_eq : oc1_179 = Nat.shiftLeft (maskOfK cm7_0 22154) 64 := by decide +kernel
theorem oc3_179_eq : oc3_179 = Nat.shiftLeft (maskOfK cm7_2 22154) 64 := by decide +kernel
theorem oc1_180_eq : oc1_180 = Nat.shiftLeft (maskOfK cm7_0 1706) 64 := by decide +kernel
theorem oc3_180_eq : oc3_180 = Nat.shiftLeft (maskOfK cm7_2 1706) 64 := by decide +kernel
theorem oc1_181_eq : oc1_181 = Nat.shiftLeft (maskOfK cm7_0 18090) 64 := by decide +kernel
theorem oc3_181_eq : oc3_181 = Nat.shiftLeft (maskOfK cm7_2 18090) 64 := by decide +kernel
end CDCert.K6
