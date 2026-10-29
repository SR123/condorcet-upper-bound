/-
CDCert.K6.Seven.S05 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 5**
(seed type 2, top slice T_6).

* `seven_leaves_5`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_5_k` of `CDCert.K6.Seven.L05_*`, 26 chunks, 512 final states);
* `seven_fam_5`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[2]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_5`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D05
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.FamB
import CDCert.K6.Seven.L05_00
import CDCert.K6.Seven.L05_01

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_5 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_5).keys = true := by
  rw [finT_5_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin5_0, fin5_1, fin5_2, fin5_3, fin5_4, fin5_5, fin5_6, fin5_7, fin5_8, fin5_9, fin5_10, fin5_11, fin5_12, fin5_13, fin5_14, fin5_15, fin5_16, fin5_17, fin5_18, fin5_19] ++ ([fin5_20, fin5_21, fin5_22, fin5_23, fin5_24, fin5_25, fin5_26, fin5_27, fin5_28, fin5_29, fin5_30, fin5_31, fin5_32, fin5_33, fin5_34, fin5_35, fin5_36, fin5_37, fin5_38, fin5_39] ++ ([fin5_40, fin5_41, fin5_42, fin5_43, fin5_44, fin5_45, fin5_46, fin5_47, fin5_48, fin5_49, fin5_50, fin5_51, fin5_52, fin5_53, fin5_54, fin5_55, fin5_56, fin5_57, fin5_58, fin5_59] ++ ([fin5_60, fin5_61, fin5_62, fin5_63, fin5_64, fin5_65, fin5_66, fin5_67, fin5_68, fin5_69, fin5_70, fin5_71, fin5_72, fin5_73, fin5_74, fin5_75, fin5_76, fin5_77, fin5_78, fin5_79] ++ ([fin5_80, fin5_81, fin5_82, fin5_83, fin5_84, fin5_85, fin5_86, fin5_87, fin5_88, fin5_89, fin5_90, fin5_91, fin5_92, fin5_93, fin5_94, fin5_95, fin5_96, fin5_97, fin5_98, fin5_99] ++ ([fin5_100, fin5_101, fin5_102, fin5_103, fin5_104, fin5_105, fin5_106, fin5_107, fin5_108, fin5_109, fin5_110, fin5_111, fin5_112, fin5_113, fin5_114, fin5_115, fin5_116, fin5_117, fin5_118, fin5_119] ++ ([fin5_120, fin5_121, fin5_122, fin5_123, fin5_124, fin5_125, fin5_126, fin5_127, fin5_128, fin5_129, fin5_130, fin5_131, fin5_132, fin5_133, fin5_134, fin5_135, fin5_136, fin5_137, fin5_138, fin5_139] ++ ([fin5_140, fin5_141, fin5_142, fin5_143, fin5_144, fin5_145, fin5_146, fin5_147, fin5_148, fin5_149, fin5_150, fin5_151, fin5_152, fin5_153, fin5_154, fin5_155, fin5_156, fin5_157, fin5_158, fin5_159] ++ ([fin5_160, fin5_161, fin5_162, fin5_163, fin5_164, fin5_165, fin5_166, fin5_167, fin5_168, fin5_169, fin5_170, fin5_171, fin5_172, fin5_173, fin5_174, fin5_175, fin5_176, fin5_177, fin5_178, fin5_179] ++ ([fin5_180, fin5_181, fin5_182, fin5_183, fin5_184, fin5_185, fin5_186, fin5_187, fin5_188, fin5_189, fin5_190, fin5_191, fin5_192, fin5_193, fin5_194, fin5_195, fin5_196, fin5_197, fin5_198, fin5_199] ++ ([fin5_200, fin5_201, fin5_202, fin5_203, fin5_204, fin5_205, fin5_206, fin5_207, fin5_208, fin5_209, fin5_210, fin5_211, fin5_212, fin5_213, fin5_214, fin5_215, fin5_216, fin5_217, fin5_218, fin5_219] ++ ([fin5_220, fin5_221, fin5_222, fin5_223, fin5_224, fin5_225, fin5_226, fin5_227, fin5_228, fin5_229, fin5_230, fin5_231, fin5_232, fin5_233, fin5_234, fin5_235, fin5_236, fin5_237, fin5_238, fin5_239] ++ ([fin5_240, fin5_241, fin5_242, fin5_243, fin5_244, fin5_245, fin5_246, fin5_247, fin5_248, fin5_249, fin5_250, fin5_251, fin5_252, fin5_253, fin5_254, fin5_255, fin5_256, fin5_257, fin5_258, fin5_259] ++ ([fin5_260, fin5_261, fin5_262, fin5_263, fin5_264, fin5_265, fin5_266, fin5_267, fin5_268, fin5_269, fin5_270, fin5_271, fin5_272, fin5_273, fin5_274, fin5_275, fin5_276, fin5_277, fin5_278, fin5_279] ++ ([fin5_280, fin5_281, fin5_282, fin5_283, fin5_284, fin5_285, fin5_286, fin5_287, fin5_288, fin5_289, fin5_290, fin5_291, fin5_292, fin5_293, fin5_294, fin5_295, fin5_296, fin5_297, fin5_298, fin5_299] ++ ([fin5_300, fin5_301, fin5_302, fin5_303, fin5_304, fin5_305, fin5_306, fin5_307, fin5_308, fin5_309, fin5_310, fin5_311, fin5_312, fin5_313, fin5_314, fin5_315, fin5_316, fin5_317, fin5_318, fin5_319] ++ ([fin5_320, fin5_321, fin5_322, fin5_323, fin5_324, fin5_325, fin5_326, fin5_327, fin5_328, fin5_329, fin5_330, fin5_331, fin5_332, fin5_333, fin5_334, fin5_335, fin5_336, fin5_337, fin5_338, fin5_339] ++ ([fin5_340, fin5_341, fin5_342, fin5_343, fin5_344, fin5_345, fin5_346, fin5_347, fin5_348, fin5_349, fin5_350, fin5_351, fin5_352, fin5_353, fin5_354, fin5_355, fin5_356, fin5_357, fin5_358, fin5_359] ++ ([fin5_360, fin5_361, fin5_362, fin5_363, fin5_364, fin5_365, fin5_366, fin5_367, fin5_368, fin5_369, fin5_370, fin5_371, fin5_372, fin5_373, fin5_374, fin5_375, fin5_376, fin5_377, fin5_378, fin5_379] ++ ([fin5_380, fin5_381, fin5_382, fin5_383, fin5_384, fin5_385, fin5_386, fin5_387, fin5_388, fin5_389, fin5_390, fin5_391, fin5_392, fin5_393, fin5_394, fin5_395, fin5_396, fin5_397, fin5_398, fin5_399] ++ ([fin5_400, fin5_401, fin5_402, fin5_403, fin5_404, fin5_405, fin5_406, fin5_407, fin5_408, fin5_409, fin5_410, fin5_411, fin5_412, fin5_413, fin5_414, fin5_415, fin5_416, fin5_417, fin5_418, fin5_419] ++ ([fin5_420, fin5_421, fin5_422, fin5_423, fin5_424, fin5_425, fin5_426, fin5_427, fin5_428, fin5_429, fin5_430, fin5_431, fin5_432, fin5_433, fin5_434, fin5_435, fin5_436, fin5_437, fin5_438, fin5_439] ++ ([fin5_440, fin5_441, fin5_442, fin5_443, fin5_444, fin5_445, fin5_446, fin5_447, fin5_448, fin5_449, fin5_450, fin5_451, fin5_452, fin5_453, fin5_454, fin5_455, fin5_456, fin5_457, fin5_458, fin5_459] ++ ([fin5_460, fin5_461, fin5_462, fin5_463, fin5_464, fin5_465, fin5_466, fin5_467, fin5_468, fin5_469, fin5_470, fin5_471, fin5_472, fin5_473, fin5_474, fin5_475, fin5_476, fin5_477, fin5_478, fin5_479] ++ ([fin5_480, fin5_481, fin5_482, fin5_483, fin5_484, fin5_485, fin5_486, fin5_487, fin5_488, fin5_489, fin5_490, fin5_491, fin5_492, fin5_493, fin5_494, fin5_495, fin5_496, fin5_497, fin5_498, fin5_499] ++ ([fin5_500, fin5_501, fin5_502, fin5_503, fin5_504, fin5_505, fin5_506, fin5_507, fin5_508, fin5_509, fin5_510, fin5_511])))))))))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_5_0, Bool.true_and, allNat_append', seven_leaf_5_1, Bool.true_and, allNat_append', seven_leaf_5_2, Bool.true_and, allNat_append', seven_leaf_5_3, Bool.true_and, allNat_append', seven_leaf_5_4, Bool.true_and, allNat_append', seven_leaf_5_5, Bool.true_and, allNat_append', seven_leaf_5_6, Bool.true_and, allNat_append', seven_leaf_5_7, Bool.true_and, allNat_append', seven_leaf_5_8, Bool.true_and, allNat_append', seven_leaf_5_9, Bool.true_and, allNat_append', seven_leaf_5_10, Bool.true_and, allNat_append', seven_leaf_5_11, Bool.true_and, allNat_append', seven_leaf_5_12, Bool.true_and, allNat_append', seven_leaf_5_13, Bool.true_and, allNat_append', seven_leaf_5_14, Bool.true_and, allNat_append', seven_leaf_5_15, Bool.true_and, allNat_append', seven_leaf_5_16, Bool.true_and, allNat_append', seven_leaf_5_17, Bool.true_and, allNat_append', seven_leaf_5_18, Bool.true_and, allNat_append', seven_leaf_5_19, Bool.true_and, allNat_append', seven_leaf_5_20, Bool.true_and, allNat_append', seven_leaf_5_21, Bool.true_and, allNat_append', seven_leaf_5_22, Bool.true_and, allNat_append', seven_leaf_5_23, Bool.true_and, allNat_append', seven_leaf_5_24, Bool.true_and]
  exact seven_leaf_5_25

theorem seven_fam_5 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 2 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 2 0 := seed7_5
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7b_5 ord7b_5_perm (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_5 (by rw [← fam7b_5_eq]; exact seven_dfs_5) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_5 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
