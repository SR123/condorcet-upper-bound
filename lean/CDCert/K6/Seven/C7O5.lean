/-
CDCert.K6.Seven.C7O5 — part of kernel checks of the seven-level option data (option masks, part 5) (Claude's generator
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

theorem oc3_227_eq : oc3_227 = Nat.shiftLeft (maskOfK cm7_2 25) 64 := by decide +kernel
theorem oc1_228_eq : oc1_228 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_228_eq : oc3_228 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_229_eq : oc1_229 = Nat.shiftLeft (maskOfK cm7_0 69) 64 := by decide +kernel
theorem oc3_229_eq : oc3_229 = Nat.shiftLeft (maskOfK cm7_2 69) 64 := by decide +kernel
theorem oc1_230_eq : oc1_230 = Nat.shiftLeft (maskOfK cm7_0 41) 64 := by decide +kernel
theorem oc3_230_eq : oc3_230 = Nat.shiftLeft (maskOfK cm7_2 41) 64 := by decide +kernel
theorem oc1_231_eq : oc1_231 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_231_eq : oc3_231 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_232_eq : oc1_232 = Nat.shiftLeft (maskOfK cm7_0 101) 64 := by decide +kernel
theorem oc3_232_eq : oc3_232 = Nat.shiftLeft (maskOfK cm7_2 101) 64 := by decide +kernel
theorem oc1_233_eq : oc1_233 = Nat.shiftLeft (maskOfK cm7_0 45) 64 := by decide +kernel
theorem oc3_233_eq : oc3_233 = Nat.shiftLeft (maskOfK cm7_2 45) 64 := by decide +kernel
theorem oc1_234_eq : oc1_234 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_234_eq : oc3_234 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_235_eq : oc1_235 = Nat.shiftLeft (maskOfK cm7_0 133) 64 := by decide +kernel
theorem oc3_235_eq : oc3_235 = Nat.shiftLeft (maskOfK cm7_2 133) 64 := by decide +kernel
theorem oc1_236_eq : oc1_236 = Nat.shiftLeft (maskOfK cm7_0 49) 64 := by decide +kernel
theorem oc3_236_eq : oc3_236 = Nat.shiftLeft (maskOfK cm7_2 49) 64 := by decide +kernel
theorem oc1_237_eq : oc1_237 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_237_eq : oc3_237 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_238_eq : oc1_238 = Nat.shiftLeft (maskOfK cm7_0 165) 64 := by decide +kernel
theorem oc3_238_eq : oc3_238 = Nat.shiftLeft (maskOfK cm7_2 165) 64 := by decide +kernel
theorem oc1_239_eq : oc1_239 = Nat.shiftLeft (maskOfK cm7_0 53) 64 := by decide +kernel
theorem oc3_239_eq : oc3_239 = Nat.shiftLeft (maskOfK cm7_2 53) 64 := by decide +kernel
theorem oc1_240_eq : oc1_240 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_240_eq : oc3_240 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_241_eq : oc1_241 = Nat.shiftLeft (maskOfK cm7_0 197) 64 := by decide +kernel
theorem oc3_241_eq : oc3_241 = Nat.shiftLeft (maskOfK cm7_2 197) 64 := by decide +kernel
theorem oc1_242_eq : oc1_242 = Nat.shiftLeft (maskOfK cm7_0 57) 64 := by decide +kernel
theorem oc3_242_eq : oc3_242 = Nat.shiftLeft (maskOfK cm7_2 57) 64 := by decide +kernel
theorem oc1_243_eq : oc1_243 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_243_eq : oc3_243 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_244_eq : oc1_244 = Nat.shiftLeft (maskOfK cm7_0 105) 64 := by decide +kernel
theorem oc3_244_eq : oc3_244 = Nat.shiftLeft (maskOfK cm7_2 105) 64 := by decide +kernel
theorem oc1_245_eq : oc1_245 = Nat.shiftLeft (maskOfK cm7_0 77) 64 := by decide +kernel
theorem oc3_245_eq : oc3_245 = Nat.shiftLeft (maskOfK cm7_2 77) 64 := by decide +kernel
theorem oc1_246_eq : oc1_246 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_246_eq : oc3_246 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_247_eq : oc1_247 = Nat.shiftLeft (maskOfK cm7_0 137) 64 := by decide +kernel
theorem oc3_247_eq : oc3_247 = Nat.shiftLeft (maskOfK cm7_2 137) 64 := by decide +kernel
theorem oc1_248_eq : oc1_248 = Nat.shiftLeft (maskOfK cm7_0 81) 64 := by decide +kernel
theorem oc3_248_eq : oc3_248 = Nat.shiftLeft (maskOfK cm7_2 81) 64 := by decide +kernel
theorem oc1_249_eq : oc1_249 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_249_eq : oc3_249 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_250_eq : oc1_250 = Nat.shiftLeft (maskOfK cm7_0 169) 64 := by decide +kernel
theorem oc3_250_eq : oc3_250 = Nat.shiftLeft (maskOfK cm7_2 169) 64 := by decide +kernel
theorem oc1_251_eq : oc1_251 = Nat.shiftLeft (maskOfK cm7_0 85) 64 := by decide +kernel
theorem oc3_251_eq : oc3_251 = Nat.shiftLeft (maskOfK cm7_2 85) 64 := by decide +kernel
theorem oc1_252_eq : oc1_252 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_252_eq : oc3_252 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_253_eq : oc1_253 = Nat.shiftLeft (maskOfK cm7_0 201) 64 := by decide +kernel
theorem oc3_253_eq : oc3_253 = Nat.shiftLeft (maskOfK cm7_2 201) 64 := by decide +kernel
theorem oc1_254_eq : oc1_254 = Nat.shiftLeft (maskOfK cm7_0 89) 64 := by decide +kernel
theorem oc3_254_eq : oc3_254 = Nat.shiftLeft (maskOfK cm7_2 89) 64 := by decide +kernel
theorem oc1_255_eq : oc1_255 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_255_eq : oc3_255 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_256_eq : oc1_256 = Nat.shiftLeft (maskOfK cm7_0 141) 64 := by decide +kernel
theorem oc3_256_eq : oc3_256 = Nat.shiftLeft (maskOfK cm7_2 141) 64 := by decide +kernel
theorem oc1_257_eq : oc1_257 = Nat.shiftLeft (maskOfK cm7_0 113) 64 := by decide +kernel
theorem oc3_257_eq : oc3_257 = Nat.shiftLeft (maskOfK cm7_2 113) 64 := by decide +kernel
theorem oc1_258_eq : oc1_258 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_258_eq : oc3_258 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_259_eq : oc1_259 = Nat.shiftLeft (maskOfK cm7_0 173) 64 := by decide +kernel
theorem oc3_259_eq : oc3_259 = Nat.shiftLeft (maskOfK cm7_2 173) 64 := by decide +kernel
theorem oc1_260_eq : oc1_260 = Nat.shiftLeft (maskOfK cm7_0 117) 64 := by decide +kernel
theorem oc3_260_eq : oc3_260 = Nat.shiftLeft (maskOfK cm7_2 117) 64 := by decide +kernel
theorem oc1_261_eq : oc1_261 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_261_eq : oc3_261 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_262_eq : oc1_262 = Nat.shiftLeft (maskOfK cm7_0 205) 64 := by decide +kernel
theorem oc3_262_eq : oc3_262 = Nat.shiftLeft (maskOfK cm7_2 205) 64 := by decide +kernel
theorem oc1_263_eq : oc1_263 = Nat.shiftLeft (maskOfK cm7_0 121) 64 := by decide +kernel
theorem oc3_263_eq : oc3_263 = Nat.shiftLeft (maskOfK cm7_2 121) 64 := by decide +kernel
theorem oc1_264_eq : oc1_264 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_264_eq : oc3_264 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_265_eq : oc1_265 = Nat.shiftLeft (maskOfK cm7_0 177) 64 := by decide +kernel
theorem oc3_265_eq : oc3_265 = Nat.shiftLeft (maskOfK cm7_2 177) 64 := by decide +kernel
theorem oc1_266_eq : oc1_266 = Nat.shiftLeft (maskOfK cm7_0 149) 64 := by decide +kernel
theorem oc3_266_eq : oc3_266 = Nat.shiftLeft (maskOfK cm7_2 149) 64 := by decide +kernel
theorem oc1_267_eq : oc1_267 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_267_eq : oc3_267 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_268_eq : oc1_268 = Nat.shiftLeft (maskOfK cm7_0 209) 64 := by decide +kernel
theorem oc3_268_eq : oc3_268 = Nat.shiftLeft (maskOfK cm7_2 209) 64 := by decide +kernel
theorem oc1_269_eq : oc1_269 = Nat.shiftLeft (maskOfK cm7_0 153) 64 := by decide +kernel
theorem oc3_269_eq : oc3_269 = Nat.shiftLeft (maskOfK cm7_2 153) 64 := by decide +kernel
theorem oc1_270_eq : oc1_270 = Nat.shiftLeft (maskOfK cm7_0 0) 64 := by decide +kernel
theorem oc3_270_eq : oc3_270 = Nat.shiftLeft (maskOfK cm7_2 0) 64 := by decide +kernel
theorem oc1_271_eq : oc1_271 = Nat.shiftLeft (maskOfK cm7_0 213) 64 := by decide +kernel
theorem oc3_271_eq : oc3_271 = Nat.shiftLeft (maskOfK cm7_2 213) 64 := by decide +kernel
theorem oc1_272_eq : oc1_272 = Nat.shiftLeft (maskOfK cm7_0 185) 64 := by decide +kernel
theorem oc3_272_eq : oc3_272 = Nat.shiftLeft (maskOfK cm7_2 185) 64 := by decide +kernel

end CDCert.K6
