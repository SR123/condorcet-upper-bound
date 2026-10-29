/-
CDCert.K6.Seven.S07 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 7**
(seed type 3, top slice T_6).

* `seven_leaves_7`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_7_k` of `CDCert.K6.Seven.L07_*`, 23 chunks, 441 final states);
* `seven_fam_7`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[3]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_7`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D07
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L07_00
import CDCert.K6.Seven.L07_01

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_7 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_7).keys = true := by
  rw [finT_7_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin7_0, fin7_1, fin7_2, fin7_3, fin7_4, fin7_5, fin7_6, fin7_7, fin7_8, fin7_9, fin7_10, fin7_11, fin7_12, fin7_13, fin7_14, fin7_15, fin7_16, fin7_17, fin7_18, fin7_19] ++ ([fin7_20, fin7_21, fin7_22, fin7_23, fin7_24, fin7_25, fin7_26, fin7_27, fin7_28, fin7_29, fin7_30, fin7_31, fin7_32, fin7_33, fin7_34, fin7_35, fin7_36, fin7_37, fin7_38, fin7_39] ++ ([fin7_40, fin7_41, fin7_42, fin7_43, fin7_44, fin7_45, fin7_46, fin7_47, fin7_48, fin7_49, fin7_50, fin7_51, fin7_52, fin7_53, fin7_54, fin7_55, fin7_56, fin7_57, fin7_58, fin7_59] ++ ([fin7_60, fin7_61, fin7_62, fin7_63, fin7_64, fin7_65, fin7_66, fin7_67, fin7_68, fin7_69, fin7_70, fin7_71, fin7_72, fin7_73, fin7_74, fin7_75, fin7_76, fin7_77, fin7_78, fin7_79] ++ ([fin7_80, fin7_81, fin7_82, fin7_83, fin7_84, fin7_85, fin7_86, fin7_87, fin7_88, fin7_89, fin7_90, fin7_91, fin7_92, fin7_93, fin7_94, fin7_95, fin7_96, fin7_97, fin7_98, fin7_99] ++ ([fin7_100, fin7_101, fin7_102, fin7_103, fin7_104, fin7_105, fin7_106, fin7_107, fin7_108, fin7_109, fin7_110, fin7_111, fin7_112, fin7_113, fin7_114, fin7_115, fin7_116, fin7_117, fin7_118, fin7_119] ++ ([fin7_120, fin7_121, fin7_122, fin7_123, fin7_124, fin7_125, fin7_126, fin7_127, fin7_128, fin7_129, fin7_130, fin7_131, fin7_132, fin7_133, fin7_134, fin7_135, fin7_136, fin7_137, fin7_138, fin7_139] ++ ([fin7_140, fin7_141, fin7_142, fin7_143, fin7_144, fin7_145, fin7_146, fin7_147, fin7_148, fin7_149, fin7_150, fin7_151, fin7_152, fin7_153, fin7_154, fin7_155, fin7_156, fin7_157, fin7_158, fin7_159] ++ ([fin7_160, fin7_161, fin7_162, fin7_163, fin7_164, fin7_165, fin7_166, fin7_167, fin7_168, fin7_169, fin7_170, fin7_171, fin7_172, fin7_173, fin7_174, fin7_175, fin7_176, fin7_177, fin7_178, fin7_179] ++ ([fin7_180, fin7_181, fin7_182, fin7_183, fin7_184, fin7_185, fin7_186, fin7_187, fin7_188, fin7_189, fin7_190, fin7_191, fin7_192, fin7_193, fin7_194, fin7_195, fin7_196, fin7_197, fin7_198, fin7_199] ++ ([fin7_200, fin7_201, fin7_202, fin7_203, fin7_204, fin7_205, fin7_206, fin7_207, fin7_208, fin7_209, fin7_210, fin7_211, fin7_212, fin7_213, fin7_214, fin7_215, fin7_216, fin7_217, fin7_218, fin7_219] ++ ([fin7_220, fin7_221, fin7_222, fin7_223, fin7_224, fin7_225, fin7_226, fin7_227, fin7_228, fin7_229, fin7_230, fin7_231, fin7_232, fin7_233, fin7_234, fin7_235, fin7_236, fin7_237, fin7_238, fin7_239] ++ ([fin7_240, fin7_241, fin7_242, fin7_243, fin7_244, fin7_245, fin7_246, fin7_247, fin7_248, fin7_249, fin7_250, fin7_251, fin7_252, fin7_253, fin7_254, fin7_255, fin7_256, fin7_257, fin7_258, fin7_259] ++ ([fin7_260, fin7_261, fin7_262, fin7_263, fin7_264, fin7_265, fin7_266, fin7_267, fin7_268, fin7_269, fin7_270, fin7_271, fin7_272, fin7_273, fin7_274, fin7_275, fin7_276, fin7_277, fin7_278, fin7_279] ++ ([fin7_280, fin7_281, fin7_282, fin7_283, fin7_284, fin7_285, fin7_286, fin7_287, fin7_288, fin7_289, fin7_290, fin7_291, fin7_292, fin7_293, fin7_294, fin7_295, fin7_296, fin7_297, fin7_298, fin7_299] ++ ([fin7_300, fin7_301, fin7_302, fin7_303, fin7_304, fin7_305, fin7_306, fin7_307, fin7_308, fin7_309, fin7_310, fin7_311, fin7_312, fin7_313, fin7_314, fin7_315, fin7_316, fin7_317, fin7_318, fin7_319] ++ ([fin7_320, fin7_321, fin7_322, fin7_323, fin7_324, fin7_325, fin7_326, fin7_327, fin7_328, fin7_329, fin7_330, fin7_331, fin7_332, fin7_333, fin7_334, fin7_335, fin7_336, fin7_337, fin7_338, fin7_339] ++ ([fin7_340, fin7_341, fin7_342, fin7_343, fin7_344, fin7_345, fin7_346, fin7_347, fin7_348, fin7_349, fin7_350, fin7_351, fin7_352, fin7_353, fin7_354, fin7_355, fin7_356, fin7_357, fin7_358, fin7_359] ++ ([fin7_360, fin7_361, fin7_362, fin7_363, fin7_364, fin7_365, fin7_366, fin7_367, fin7_368, fin7_369, fin7_370, fin7_371, fin7_372, fin7_373, fin7_374, fin7_375, fin7_376, fin7_377, fin7_378, fin7_379] ++ ([fin7_380, fin7_381, fin7_382, fin7_383, fin7_384, fin7_385, fin7_386, fin7_387, fin7_388, fin7_389, fin7_390, fin7_391, fin7_392, fin7_393, fin7_394, fin7_395, fin7_396, fin7_397, fin7_398, fin7_399] ++ ([fin7_400, fin7_401, fin7_402, fin7_403, fin7_404, fin7_405, fin7_406, fin7_407, fin7_408, fin7_409, fin7_410, fin7_411, fin7_412, fin7_413, fin7_414, fin7_415, fin7_416, fin7_417, fin7_418, fin7_419] ++ ([fin7_420, fin7_421, fin7_422, fin7_423, fin7_424, fin7_425, fin7_426, fin7_427, fin7_428, fin7_429, fin7_430, fin7_431, fin7_432, fin7_433, fin7_434, fin7_435, fin7_436, fin7_437, fin7_438, fin7_439] ++ ([fin7_440]))))))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_7_0, Bool.true_and, allNat_append', seven_leaf_7_1, Bool.true_and, allNat_append', seven_leaf_7_2, Bool.true_and, allNat_append', seven_leaf_7_3, Bool.true_and, allNat_append', seven_leaf_7_4, Bool.true_and, allNat_append', seven_leaf_7_5, Bool.true_and, allNat_append', seven_leaf_7_6, Bool.true_and, allNat_append', seven_leaf_7_7, Bool.true_and, allNat_append', seven_leaf_7_8, Bool.true_and, allNat_append', seven_leaf_7_9, Bool.true_and, allNat_append', seven_leaf_7_10, Bool.true_and, allNat_append', seven_leaf_7_11, Bool.true_and, allNat_append', seven_leaf_7_12, Bool.true_and, allNat_append', seven_leaf_7_13, Bool.true_and, allNat_append', seven_leaf_7_14, Bool.true_and, allNat_append', seven_leaf_7_15, Bool.true_and, allNat_append', seven_leaf_7_16, Bool.true_and, allNat_append', seven_leaf_7_17, Bool.true_and, allNat_append', seven_leaf_7_18, Bool.true_and, allNat_append', seven_leaf_7_19, Bool.true_and, allNat_append', seven_leaf_7_20, Bool.true_and, allNat_append', seven_leaf_7_21, Bool.true_and]
  exact seven_leaf_7_22

theorem seven_fam_7 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 3 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 3 0 := seed7_7
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_7 ord7_7_perm (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_7 (by rw [← fam7_7_eq]; exact seven_dfs_7) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_7 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
