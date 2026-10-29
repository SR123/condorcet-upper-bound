/-
CDCert.K6.Seven.C7O4 — part of kernel checks of the seven-level option data (option masks, part 4) (Claude's generator
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

theorem oc1_182_eq : oc1_182 = Nat.shiftLeft (maskOfK cm7_0 3754) 64 := by decide +kernel
theorem oc3_182_eq : oc3_182 = Nat.shiftLeft (maskOfK cm7_2 3754) 64 := by decide +kernel
theorem oc1_183_eq : oc1_183 = Nat.shiftLeft (maskOfK cm7_0 20138) 64 := by decide +kernel
theorem oc3_183_eq : oc3_183 = Nat.shiftLeft (maskOfK cm7_2 20138) 64 := by decide +kernel
theorem oc1_184_eq : oc1_184 = Nat.shiftLeft (maskOfK cm7_0 5802) 64 := by decide +kernel
theorem oc3_184_eq : oc3_184 = Nat.shiftLeft (maskOfK cm7_2 5802) 64 := by decide +kernel
theorem oc1_185_eq : oc1_185 = Nat.shiftLeft (maskOfK cm7_0 22186) 64 := by decide +kernel
theorem oc3_185_eq : oc3_185 = Nat.shiftLeft (maskOfK cm7_2 22186) 64 := by decide +kernel
theorem oc1_186_eq : oc1_186 = Nat.shiftLeft (maskOfK cm7_0 1422) 64 := by decide +kernel
theorem oc3_186_eq : oc3_186 = Nat.shiftLeft (maskOfK cm7_2 1422) 64 := by decide +kernel
theorem oc1_187_eq : oc1_187 = Nat.shiftLeft (maskOfK cm7_0 17806) 64 := by decide +kernel
theorem oc3_187_eq : oc3_187 = Nat.shiftLeft (maskOfK cm7_2 17806) 64 := by decide +kernel
theorem oc1_188_eq : oc1_188 = Nat.shiftLeft (maskOfK cm7_0 3470) 64 := by decide +kernel
theorem oc3_188_eq : oc3_188 = Nat.shiftLeft (maskOfK cm7_2 3470) 64 := by decide +kernel
theorem oc1_189_eq : oc1_189 = Nat.shiftLeft (maskOfK cm7_0 19854) 64 := by decide +kernel
theorem oc3_189_eq : oc3_189 = Nat.shiftLeft (maskOfK cm7_2 19854) 64 := by decide +kernel
theorem oc1_190_eq : oc1_190 = Nat.shiftLeft (maskOfK cm7_0 5518) 64 := by decide +kernel
theorem oc3_190_eq : oc3_190 = Nat.shiftLeft (maskOfK cm7_2 5518) 64 := by decide +kernel
theorem oc1_191_eq : oc1_191 = Nat.shiftLeft (maskOfK cm7_0 21902) 64 := by decide +kernel
theorem oc3_191_eq : oc3_191 = Nat.shiftLeft (maskOfK cm7_2 21902) 64 := by decide +kernel
theorem oc1_192_eq : oc1_192 = Nat.shiftLeft (maskOfK cm7_0 1678) 64 := by decide +kernel
theorem oc3_192_eq : oc3_192 = Nat.shiftLeft (maskOfK cm7_2 1678) 64 := by decide +kernel
theorem oc1_193_eq : oc1_193 = Nat.shiftLeft (maskOfK cm7_0 18062) 64 := by decide +kernel
theorem oc3_193_eq : oc3_193 = Nat.shiftLeft (maskOfK cm7_2 18062) 64 := by decide +kernel
theorem oc1_194_eq : oc1_194 = Nat.shiftLeft (maskOfK cm7_0 3726) 64 := by decide +kernel
theorem oc3_194_eq : oc3_194 = Nat.shiftLeft (maskOfK cm7_2 3726) 64 := by decide +kernel
theorem oc1_195_eq : oc1_195 = Nat.shiftLeft (maskOfK cm7_0 20110) 64 := by decide +kernel
theorem oc3_195_eq : oc3_195 = Nat.shiftLeft (maskOfK cm7_2 20110) 64 := by decide +kernel
theorem oc1_196_eq : oc1_196 = Nat.shiftLeft (maskOfK cm7_0 5774) 64 := by decide +kernel
theorem oc3_196_eq : oc3_196 = Nat.shiftLeft (maskOfK cm7_2 5774) 64 := by decide +kernel
theorem oc1_197_eq : oc1_197 = Nat.shiftLeft (maskOfK cm7_0 22158) 64 := by decide +kernel
theorem oc3_197_eq : oc3_197 = Nat.shiftLeft (maskOfK cm7_2 22158) 64 := by decide +kernel
theorem oc1_198_eq : oc1_198 = Nat.shiftLeft (maskOfK cm7_0 1710) 64 := by decide +kernel
theorem oc3_198_eq : oc3_198 = Nat.shiftLeft (maskOfK cm7_2 1710) 64 := by decide +kernel
theorem oc1_199_eq : oc1_199 = Nat.shiftLeft (maskOfK cm7_0 18094) 64 := by decide +kernel
theorem oc3_199_eq : oc3_199 = Nat.shiftLeft (maskOfK cm7_2 18094) 64 := by decide +kernel
theorem oc1_200_eq : oc1_200 = Nat.shiftLeft (maskOfK cm7_0 3758) 64 := by decide +kernel
theorem oc3_200_eq : oc3_200 = Nat.shiftLeft (maskOfK cm7_2 3758) 64 := by decide +kernel
theorem oc1_201_eq : oc1_201 = Nat.shiftLeft (maskOfK cm7_0 20142) 64 := by decide +kernel
theorem oc3_201_eq : oc3_201 = Nat.shiftLeft (maskOfK cm7_2 20142) 64 := by decide +kernel
theorem oc1_202_eq : oc1_202 = Nat.shiftLeft (maskOfK cm7_0 5806) 64 := by decide +kernel
theorem oc3_202_eq : oc3_202 = Nat.shiftLeft (maskOfK cm7_2 5806) 64 := by decide +kernel
theorem oc1_203_eq : oc1_203 = Nat.shiftLeft (maskOfK cm7_0 22190) 64 := by decide +kernel
theorem oc3_203_eq : oc3_203 = Nat.shiftLeft (maskOfK cm7_2 22190) 64 := by decide +kernel
theorem oc1_204_eq : oc1_204 = Nat.shiftLeft (maskOfK cm7_0 1714) 64 := by decide +kernel
theorem oc3_204_eq : oc3_204 = Nat.shiftLeft (maskOfK cm7_2 1714) 64 := by decide +kernel
theorem oc1_205_eq : oc1_205 = Nat.shiftLeft (maskOfK cm7_0 18098) 64 := by decide +kernel
theorem oc3_205_eq : oc3_205 = Nat.shiftLeft (maskOfK cm7_2 18098) 64 := by decide +kernel
theorem oc1_206_eq : oc1_206 = Nat.shiftLeft (maskOfK cm7_0 3762) 64 := by decide +kernel
theorem oc3_206_eq : oc3_206 = Nat.shiftLeft (maskOfK cm7_2 3762) 64 := by decide +kernel
theorem oc1_207_eq : oc1_207 = Nat.shiftLeft (maskOfK cm7_0 20146) 64 := by decide +kernel
theorem oc3_207_eq : oc3_207 = Nat.shiftLeft (maskOfK cm7_2 20146) 64 := by decide +kernel
theorem oc1_208_eq : oc1_208 = Nat.shiftLeft (maskOfK cm7_0 5810) 64 := by decide +kernel
theorem oc3_208_eq : oc3_208 = Nat.shiftLeft (maskOfK cm7_2 5810) 64 := by decide +kernel
theorem oc1_209_eq : oc1_209 = Nat.shiftLeft (maskOfK cm7_0 22194) 64 := by decide +kernel
theorem oc3_209_eq : oc3_209 = Nat.shiftLeft (maskOfK cm7_2 22194) 64 := by decide +kernel
theorem oc1_210_eq : oc1_210 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_210_eq : oc3_210 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_211_eq : oc1_211 = Nat.shiftLeft (maskOfK cm7_0 33) 64 := by decide +kernel
theorem oc3_211_eq : oc3_211 = Nat.shiftLeft (maskOfK cm7_2 33) 64 := by decide +kernel
theorem oc1_212_eq : oc1_212 = Nat.shiftLeft (maskOfK cm7_0 5) 64 := by decide +kernel
theorem oc3_212_eq : oc3_212 = Nat.shiftLeft (maskOfK cm7_2 5) 64 := by decide +kernel
theorem oc1_213_eq : oc1_213 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_213_eq : oc3_213 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_214_eq : oc1_214 = Nat.shiftLeft (maskOfK cm7_0 65) 64 := by decide +kernel
theorem oc3_214_eq : oc3_214 = Nat.shiftLeft (maskOfK cm7_2 65) 64 := by decide +kernel
theorem oc1_215_eq : oc1_215 = Nat.shiftLeft (maskOfK cm7_0 9) 64 := by decide +kernel
theorem oc3_215_eq : oc3_215 = Nat.shiftLeft (maskOfK cm7_2 9) 64 := by decide +kernel
theorem oc1_216_eq : oc1_216 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_216_eq : oc3_216 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_217_eq : oc1_217 = Nat.shiftLeft (maskOfK cm7_0 97) 64 := by decide +kernel
theorem oc3_217_eq : oc3_217 = Nat.shiftLeft (maskOfK cm7_2 97) 64 := by decide +kernel
theorem oc1_218_eq : oc1_218 = Nat.shiftLeft (maskOfK cm7_0 13) 64 := by decide +kernel
theorem oc3_218_eq : oc3_218 = Nat.shiftLeft (maskOfK cm7_2 13) 64 := by decide +kernel
theorem oc1_219_eq : oc1_219 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_219_eq : oc3_219 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_220_eq : oc1_220 = Nat.shiftLeft (maskOfK cm7_0 129) 64 := by decide +kernel
theorem oc3_220_eq : oc3_220 = Nat.shiftLeft (maskOfK cm7_2 129) 64 := by decide +kernel
theorem oc1_221_eq : oc1_221 = Nat.shiftLeft (maskOfK cm7_0 17) 64 := by decide +kernel
theorem oc3_221_eq : oc3_221 = Nat.shiftLeft (maskOfK cm7_2 17) 64 := by decide +kernel
theorem oc1_222_eq : oc1_222 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_222_eq : oc3_222 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_223_eq : oc1_223 = Nat.shiftLeft (maskOfK cm7_0 161) 64 := by decide +kernel
theorem oc3_223_eq : oc3_223 = Nat.shiftLeft (maskOfK cm7_2 161) 64 := by decide +kernel
theorem oc1_224_eq : oc1_224 = Nat.shiftLeft (maskOfK cm7_0 21) 64 := by decide +kernel
theorem oc3_224_eq : oc3_224 = Nat.shiftLeft (maskOfK cm7_2 21) 64 := by decide +kernel
theorem oc1_225_eq : oc1_225 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_225_eq : oc3_225 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_226_eq : oc1_226 = Nat.shiftLeft (maskOfK cm7_0 193) 64 := by decide +kernel
theorem oc3_226_eq : oc3_226 = Nat.shiftLeft (maskOfK cm7_2 193) 64 := by decide +kernel
theorem oc1_227_eq : oc1_227 = Nat.shiftLeft (maskOfK cm7_0 25) 64 := by decide +kernel
end CDCert.K6
