/-
CDCert.K6.Seven.S08 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 8**
(seed type 4, bottom slice B_6).

* `seven_leaves_8`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_8_k` of `CDCert.K6.Seven.L08_*`, 19 chunks, 375 final states);
* `seven_fam_8`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[4]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_8`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D08
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L08_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_8 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_8).keys = true := by
  rw [finT_8_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin8_0, fin8_1, fin8_2, fin8_3, fin8_4, fin8_5, fin8_6, fin8_7, fin8_8, fin8_9, fin8_10, fin8_11, fin8_12, fin8_13, fin8_14, fin8_15, fin8_16, fin8_17, fin8_18, fin8_19] ++ ([fin8_20, fin8_21, fin8_22, fin8_23, fin8_24, fin8_25, fin8_26, fin8_27, fin8_28, fin8_29, fin8_30, fin8_31, fin8_32, fin8_33, fin8_34, fin8_35, fin8_36, fin8_37, fin8_38, fin8_39] ++ ([fin8_40, fin8_41, fin8_42, fin8_43, fin8_44, fin8_45, fin8_46, fin8_47, fin8_48, fin8_49, fin8_50, fin8_51, fin8_52, fin8_53, fin8_54, fin8_55, fin8_56, fin8_57, fin8_58, fin8_59] ++ ([fin8_60, fin8_61, fin8_62, fin8_63, fin8_64, fin8_65, fin8_66, fin8_67, fin8_68, fin8_69, fin8_70, fin8_71, fin8_72, fin8_73, fin8_74, fin8_75, fin8_76, fin8_77, fin8_78, fin8_79] ++ ([fin8_80, fin8_81, fin8_82, fin8_83, fin8_84, fin8_85, fin8_86, fin8_87, fin8_88, fin8_89, fin8_90, fin8_91, fin8_92, fin8_93, fin8_94, fin8_95, fin8_96, fin8_97, fin8_98, fin8_99] ++ ([fin8_100, fin8_101, fin8_102, fin8_103, fin8_104, fin8_105, fin8_106, fin8_107, fin8_108, fin8_109, fin8_110, fin8_111, fin8_112, fin8_113, fin8_114, fin8_115, fin8_116, fin8_117, fin8_118, fin8_119] ++ ([fin8_120, fin8_121, fin8_122, fin8_123, fin8_124, fin8_125, fin8_126, fin8_127, fin8_128, fin8_129, fin8_130, fin8_131, fin8_132, fin8_133, fin8_134, fin8_135, fin8_136, fin8_137, fin8_138, fin8_139] ++ ([fin8_140, fin8_141, fin8_142, fin8_143, fin8_144, fin8_145, fin8_146, fin8_147, fin8_148, fin8_149, fin8_150, fin8_151, fin8_152, fin8_153, fin8_154, fin8_155, fin8_156, fin8_157, fin8_158, fin8_159] ++ ([fin8_160, fin8_161, fin8_162, fin8_163, fin8_164, fin8_165, fin8_166, fin8_167, fin8_168, fin8_169, fin8_170, fin8_171, fin8_172, fin8_173, fin8_174, fin8_175, fin8_176, fin8_177, fin8_178, fin8_179] ++ ([fin8_180, fin8_181, fin8_182, fin8_183, fin8_184, fin8_185, fin8_186, fin8_187, fin8_188, fin8_189, fin8_190, fin8_191, fin8_192, fin8_193, fin8_194, fin8_195, fin8_196, fin8_197, fin8_198, fin8_199] ++ ([fin8_200, fin8_201, fin8_202, fin8_203, fin8_204, fin8_205, fin8_206, fin8_207, fin8_208, fin8_209, fin8_210, fin8_211, fin8_212, fin8_213, fin8_214, fin8_215, fin8_216, fin8_217, fin8_218, fin8_219] ++ ([fin8_220, fin8_221, fin8_222, fin8_223, fin8_224, fin8_225, fin8_226, fin8_227, fin8_228, fin8_229, fin8_230, fin8_231, fin8_232, fin8_233, fin8_234, fin8_235, fin8_236, fin8_237, fin8_238, fin8_239] ++ ([fin8_240, fin8_241, fin8_242, fin8_243, fin8_244, fin8_245, fin8_246, fin8_247, fin8_248, fin8_249, fin8_250, fin8_251, fin8_252, fin8_253, fin8_254, fin8_255, fin8_256, fin8_257, fin8_258, fin8_259] ++ ([fin8_260, fin8_261, fin8_262, fin8_263, fin8_264, fin8_265, fin8_266, fin8_267, fin8_268, fin8_269, fin8_270, fin8_271, fin8_272, fin8_273, fin8_274, fin8_275, fin8_276, fin8_277, fin8_278, fin8_279] ++ ([fin8_280, fin8_281, fin8_282, fin8_283, fin8_284, fin8_285, fin8_286, fin8_287, fin8_288, fin8_289, fin8_290, fin8_291, fin8_292, fin8_293, fin8_294, fin8_295, fin8_296, fin8_297, fin8_298, fin8_299] ++ ([fin8_300, fin8_301, fin8_302, fin8_303, fin8_304, fin8_305, fin8_306, fin8_307, fin8_308, fin8_309, fin8_310, fin8_311, fin8_312, fin8_313, fin8_314, fin8_315, fin8_316, fin8_317, fin8_318, fin8_319] ++ ([fin8_320, fin8_321, fin8_322, fin8_323, fin8_324, fin8_325, fin8_326, fin8_327, fin8_328, fin8_329, fin8_330, fin8_331, fin8_332, fin8_333, fin8_334, fin8_335, fin8_336, fin8_337, fin8_338, fin8_339] ++ ([fin8_340, fin8_341, fin8_342, fin8_343, fin8_344, fin8_345, fin8_346, fin8_347, fin8_348, fin8_349, fin8_350, fin8_351, fin8_352, fin8_353, fin8_354, fin8_355, fin8_356, fin8_357, fin8_358, fin8_359] ++ ([fin8_360, fin8_361, fin8_362, fin8_363, fin8_364, fin8_365, fin8_366, fin8_367, fin8_368, fin8_369, fin8_370, fin8_371, fin8_372, fin8_373, fin8_374]))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_8_0, Bool.true_and, allNat_append', seven_leaf_8_1, Bool.true_and, allNat_append', seven_leaf_8_2, Bool.true_and, allNat_append', seven_leaf_8_3, Bool.true_and, allNat_append', seven_leaf_8_4, Bool.true_and, allNat_append', seven_leaf_8_5, Bool.true_and, allNat_append', seven_leaf_8_6, Bool.true_and, allNat_append', seven_leaf_8_7, Bool.true_and, allNat_append', seven_leaf_8_8, Bool.true_and, allNat_append', seven_leaf_8_9, Bool.true_and, allNat_append', seven_leaf_8_10, Bool.true_and, allNat_append', seven_leaf_8_11, Bool.true_and, allNat_append', seven_leaf_8_12, Bool.true_and, allNat_append', seven_leaf_8_13, Bool.true_and, allNat_append', seven_leaf_8_14, Bool.true_and, allNat_append', seven_leaf_8_15, Bool.true_and, allNat_append', seven_leaf_8_16, Bool.true_and, allNat_append', seven_leaf_8_17, Bool.true_and]
  exact seven_leaf_8_18

theorem seven_fam_8 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 4 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 4 0 := seed7_8
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_8 ord7_8_perm (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_8 (by rw [← fam7_8_eq]; exact seven_dfs_8) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_8 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
