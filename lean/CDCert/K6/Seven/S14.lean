/-
CDCert.K6.Seven.S14 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 14**
(seed type 7, bottom slice B_6).

* `seven_leaves_14`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_14_k` of `CDCert.K6.Seven.L14_*`, 20 chunks, 382 final states);
* `seven_fam_14`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[7]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_14`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D14
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L14_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_14 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_14).keys = true := by
  rw [finT_14_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin14_0, fin14_1, fin14_2, fin14_3, fin14_4, fin14_5, fin14_6, fin14_7, fin14_8, fin14_9, fin14_10, fin14_11, fin14_12, fin14_13, fin14_14, fin14_15, fin14_16, fin14_17, fin14_18, fin14_19] ++ ([fin14_20, fin14_21, fin14_22, fin14_23, fin14_24, fin14_25, fin14_26, fin14_27, fin14_28, fin14_29, fin14_30, fin14_31, fin14_32, fin14_33, fin14_34, fin14_35, fin14_36, fin14_37, fin14_38, fin14_39] ++ ([fin14_40, fin14_41, fin14_42, fin14_43, fin14_44, fin14_45, fin14_46, fin14_47, fin14_48, fin14_49, fin14_50, fin14_51, fin14_52, fin14_53, fin14_54, fin14_55, fin14_56, fin14_57, fin14_58, fin14_59] ++ ([fin14_60, fin14_61, fin14_62, fin14_63, fin14_64, fin14_65, fin14_66, fin14_67, fin14_68, fin14_69, fin14_70, fin14_71, fin14_72, fin14_73, fin14_74, fin14_75, fin14_76, fin14_77, fin14_78, fin14_79] ++ ([fin14_80, fin14_81, fin14_82, fin14_83, fin14_84, fin14_85, fin14_86, fin14_87, fin14_88, fin14_89, fin14_90, fin14_91, fin14_92, fin14_93, fin14_94, fin14_95, fin14_96, fin14_97, fin14_98, fin14_99] ++ ([fin14_100, fin14_101, fin14_102, fin14_103, fin14_104, fin14_105, fin14_106, fin14_107, fin14_108, fin14_109, fin14_110, fin14_111, fin14_112, fin14_113, fin14_114, fin14_115, fin14_116, fin14_117, fin14_118, fin14_119] ++ ([fin14_120, fin14_121, fin14_122, fin14_123, fin14_124, fin14_125, fin14_126, fin14_127, fin14_128, fin14_129, fin14_130, fin14_131, fin14_132, fin14_133, fin14_134, fin14_135, fin14_136, fin14_137, fin14_138, fin14_139] ++ ([fin14_140, fin14_141, fin14_142, fin14_143, fin14_144, fin14_145, fin14_146, fin14_147, fin14_148, fin14_149, fin14_150, fin14_151, fin14_152, fin14_153, fin14_154, fin14_155, fin14_156, fin14_157, fin14_158, fin14_159] ++ ([fin14_160, fin14_161, fin14_162, fin14_163, fin14_164, fin14_165, fin14_166, fin14_167, fin14_168, fin14_169, fin14_170, fin14_171, fin14_172, fin14_173, fin14_174, fin14_175, fin14_176, fin14_177, fin14_178, fin14_179] ++ ([fin14_180, fin14_181, fin14_182, fin14_183, fin14_184, fin14_185, fin14_186, fin14_187, fin14_188, fin14_189, fin14_190, fin14_191, fin14_192, fin14_193, fin14_194, fin14_195, fin14_196, fin14_197, fin14_198, fin14_199] ++ ([fin14_200, fin14_201, fin14_202, fin14_203, fin14_204, fin14_205, fin14_206, fin14_207, fin14_208, fin14_209, fin14_210, fin14_211, fin14_212, fin14_213, fin14_214, fin14_215, fin14_216, fin14_217, fin14_218, fin14_219] ++ ([fin14_220, fin14_221, fin14_222, fin14_223, fin14_224, fin14_225, fin14_226, fin14_227, fin14_228, fin14_229, fin14_230, fin14_231, fin14_232, fin14_233, fin14_234, fin14_235, fin14_236, fin14_237, fin14_238, fin14_239] ++ ([fin14_240, fin14_241, fin14_242, fin14_243, fin14_244, fin14_245, fin14_246, fin14_247, fin14_248, fin14_249, fin14_250, fin14_251, fin14_252, fin14_253, fin14_254, fin14_255, fin14_256, fin14_257, fin14_258, fin14_259] ++ ([fin14_260, fin14_261, fin14_262, fin14_263, fin14_264, fin14_265, fin14_266, fin14_267, fin14_268, fin14_269, fin14_270, fin14_271, fin14_272, fin14_273, fin14_274, fin14_275, fin14_276, fin14_277, fin14_278, fin14_279] ++ ([fin14_280, fin14_281, fin14_282, fin14_283, fin14_284, fin14_285, fin14_286, fin14_287, fin14_288, fin14_289, fin14_290, fin14_291, fin14_292, fin14_293, fin14_294, fin14_295, fin14_296, fin14_297, fin14_298, fin14_299] ++ ([fin14_300, fin14_301, fin14_302, fin14_303, fin14_304, fin14_305, fin14_306, fin14_307, fin14_308, fin14_309, fin14_310, fin14_311, fin14_312, fin14_313, fin14_314, fin14_315, fin14_316, fin14_317, fin14_318, fin14_319] ++ ([fin14_320, fin14_321, fin14_322, fin14_323, fin14_324, fin14_325, fin14_326, fin14_327, fin14_328, fin14_329, fin14_330, fin14_331, fin14_332, fin14_333, fin14_334, fin14_335, fin14_336, fin14_337, fin14_338, fin14_339] ++ ([fin14_340, fin14_341, fin14_342, fin14_343, fin14_344, fin14_345, fin14_346, fin14_347, fin14_348, fin14_349, fin14_350, fin14_351, fin14_352, fin14_353, fin14_354, fin14_355, fin14_356, fin14_357, fin14_358, fin14_359] ++ ([fin14_360, fin14_361, fin14_362, fin14_363, fin14_364, fin14_365, fin14_366, fin14_367, fin14_368, fin14_369, fin14_370, fin14_371, fin14_372, fin14_373, fin14_374, fin14_375, fin14_376, fin14_377, fin14_378, fin14_379] ++ ([fin14_380, fin14_381])))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_14_0, Bool.true_and, allNat_append', seven_leaf_14_1, Bool.true_and, allNat_append', seven_leaf_14_2, Bool.true_and, allNat_append', seven_leaf_14_3, Bool.true_and, allNat_append', seven_leaf_14_4, Bool.true_and, allNat_append', seven_leaf_14_5, Bool.true_and, allNat_append', seven_leaf_14_6, Bool.true_and, allNat_append', seven_leaf_14_7, Bool.true_and, allNat_append', seven_leaf_14_8, Bool.true_and, allNat_append', seven_leaf_14_9, Bool.true_and, allNat_append', seven_leaf_14_10, Bool.true_and, allNat_append', seven_leaf_14_11, Bool.true_and, allNat_append', seven_leaf_14_12, Bool.true_and, allNat_append', seven_leaf_14_13, Bool.true_and, allNat_append', seven_leaf_14_14, Bool.true_and, allNat_append', seven_leaf_14_15, Bool.true_and, allNat_append', seven_leaf_14_16, Bool.true_and, allNat_append', seven_leaf_14_17, Bool.true_and, allNat_append', seven_leaf_14_18, Bool.true_and]
  exact seven_leaf_14_19

theorem seven_fam_14 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 7 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 7 0 := seed7_14
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_14 ord7_14_perm (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_14 (by rw [← fam7_14_eq]; exact seven_dfs_14) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_14 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
