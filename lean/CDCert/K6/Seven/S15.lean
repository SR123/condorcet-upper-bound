/-
CDCert.K6.Seven.S15 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 15**
(seed type 7, top slice T_6).

* `seven_leaves_15`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_15_k` of `CDCert.K6.Seven.L15_*`, 19 chunks, 378 final states);
* `seven_fam_15`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[7]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_15`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D15
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L15_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_15 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_15).keys = true := by
  rw [finT_15_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin15_0, fin15_1, fin15_2, fin15_3, fin15_4, fin15_5, fin15_6, fin15_7, fin15_8, fin15_9, fin15_10, fin15_11, fin15_12, fin15_13, fin15_14, fin15_15, fin15_16, fin15_17, fin15_18, fin15_19] ++ ([fin15_20, fin15_21, fin15_22, fin15_23, fin15_24, fin15_25, fin15_26, fin15_27, fin15_28, fin15_29, fin15_30, fin15_31, fin15_32, fin15_33, fin15_34, fin15_35, fin15_36, fin15_37, fin15_38, fin15_39] ++ ([fin15_40, fin15_41, fin15_42, fin15_43, fin15_44, fin15_45, fin15_46, fin15_47, fin15_48, fin15_49, fin15_50, fin15_51, fin15_52, fin15_53, fin15_54, fin15_55, fin15_56, fin15_57, fin15_58, fin15_59] ++ ([fin15_60, fin15_61, fin15_62, fin15_63, fin15_64, fin15_65, fin15_66, fin15_67, fin15_68, fin15_69, fin15_70, fin15_71, fin15_72, fin15_73, fin15_74, fin15_75, fin15_76, fin15_77, fin15_78, fin15_79] ++ ([fin15_80, fin15_81, fin15_82, fin15_83, fin15_84, fin15_85, fin15_86, fin15_87, fin15_88, fin15_89, fin15_90, fin15_91, fin15_92, fin15_93, fin15_94, fin15_95, fin15_96, fin15_97, fin15_98, fin15_99] ++ ([fin15_100, fin15_101, fin15_102, fin15_103, fin15_104, fin15_105, fin15_106, fin15_107, fin15_108, fin15_109, fin15_110, fin15_111, fin15_112, fin15_113, fin15_114, fin15_115, fin15_116, fin15_117, fin15_118, fin15_119] ++ ([fin15_120, fin15_121, fin15_122, fin15_123, fin15_124, fin15_125, fin15_126, fin15_127, fin15_128, fin15_129, fin15_130, fin15_131, fin15_132, fin15_133, fin15_134, fin15_135, fin15_136, fin15_137, fin15_138, fin15_139] ++ ([fin15_140, fin15_141, fin15_142, fin15_143, fin15_144, fin15_145, fin15_146, fin15_147, fin15_148, fin15_149, fin15_150, fin15_151, fin15_152, fin15_153, fin15_154, fin15_155, fin15_156, fin15_157, fin15_158, fin15_159] ++ ([fin15_160, fin15_161, fin15_162, fin15_163, fin15_164, fin15_165, fin15_166, fin15_167, fin15_168, fin15_169, fin15_170, fin15_171, fin15_172, fin15_173, fin15_174, fin15_175, fin15_176, fin15_177, fin15_178, fin15_179] ++ ([fin15_180, fin15_181, fin15_182, fin15_183, fin15_184, fin15_185, fin15_186, fin15_187, fin15_188, fin15_189, fin15_190, fin15_191, fin15_192, fin15_193, fin15_194, fin15_195, fin15_196, fin15_197, fin15_198, fin15_199] ++ ([fin15_200, fin15_201, fin15_202, fin15_203, fin15_204, fin15_205, fin15_206, fin15_207, fin15_208, fin15_209, fin15_210, fin15_211, fin15_212, fin15_213, fin15_214, fin15_215, fin15_216, fin15_217, fin15_218, fin15_219] ++ ([fin15_220, fin15_221, fin15_222, fin15_223, fin15_224, fin15_225, fin15_226, fin15_227, fin15_228, fin15_229, fin15_230, fin15_231, fin15_232, fin15_233, fin15_234, fin15_235, fin15_236, fin15_237, fin15_238, fin15_239] ++ ([fin15_240, fin15_241, fin15_242, fin15_243, fin15_244, fin15_245, fin15_246, fin15_247, fin15_248, fin15_249, fin15_250, fin15_251, fin15_252, fin15_253, fin15_254, fin15_255, fin15_256, fin15_257, fin15_258, fin15_259] ++ ([fin15_260, fin15_261, fin15_262, fin15_263, fin15_264, fin15_265, fin15_266, fin15_267, fin15_268, fin15_269, fin15_270, fin15_271, fin15_272, fin15_273, fin15_274, fin15_275, fin15_276, fin15_277, fin15_278, fin15_279] ++ ([fin15_280, fin15_281, fin15_282, fin15_283, fin15_284, fin15_285, fin15_286, fin15_287, fin15_288, fin15_289, fin15_290, fin15_291, fin15_292, fin15_293, fin15_294, fin15_295, fin15_296, fin15_297, fin15_298, fin15_299] ++ ([fin15_300, fin15_301, fin15_302, fin15_303, fin15_304, fin15_305, fin15_306, fin15_307, fin15_308, fin15_309, fin15_310, fin15_311, fin15_312, fin15_313, fin15_314, fin15_315, fin15_316, fin15_317, fin15_318, fin15_319] ++ ([fin15_320, fin15_321, fin15_322, fin15_323, fin15_324, fin15_325, fin15_326, fin15_327, fin15_328, fin15_329, fin15_330, fin15_331, fin15_332, fin15_333, fin15_334, fin15_335, fin15_336, fin15_337, fin15_338, fin15_339] ++ ([fin15_340, fin15_341, fin15_342, fin15_343, fin15_344, fin15_345, fin15_346, fin15_347, fin15_348, fin15_349, fin15_350, fin15_351, fin15_352, fin15_353, fin15_354, fin15_355, fin15_356, fin15_357, fin15_358, fin15_359] ++ ([fin15_360, fin15_361, fin15_362, fin15_363, fin15_364, fin15_365, fin15_366, fin15_367, fin15_368, fin15_369, fin15_370, fin15_371, fin15_372, fin15_373, fin15_374, fin15_375, fin15_376, fin15_377]))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_15_0, Bool.true_and, allNat_append', seven_leaf_15_1, Bool.true_and, allNat_append', seven_leaf_15_2, Bool.true_and, allNat_append', seven_leaf_15_3, Bool.true_and, allNat_append', seven_leaf_15_4, Bool.true_and, allNat_append', seven_leaf_15_5, Bool.true_and, allNat_append', seven_leaf_15_6, Bool.true_and, allNat_append', seven_leaf_15_7, Bool.true_and, allNat_append', seven_leaf_15_8, Bool.true_and, allNat_append', seven_leaf_15_9, Bool.true_and, allNat_append', seven_leaf_15_10, Bool.true_and, allNat_append', seven_leaf_15_11, Bool.true_and, allNat_append', seven_leaf_15_12, Bool.true_and, allNat_append', seven_leaf_15_13, Bool.true_and, allNat_append', seven_leaf_15_14, Bool.true_and, allNat_append', seven_leaf_15_15, Bool.true_and, allNat_append', seven_leaf_15_16, Bool.true_and, allNat_append', seven_leaf_15_17, Bool.true_and]
  exact seven_leaf_15_18

theorem seven_fam_15 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 7 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 7 0 := seed7_15
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_15 ord7_15_perm (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_15 (by rw [← fam7_15_eq]; exact seven_dfs_15) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_15 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
