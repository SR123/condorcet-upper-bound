/-
CDCert.K6.Seven.S17 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 17**
(seed type 8, top slice T_6).

* `seven_leaves_17`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_17_k` of `CDCert.K6.Seven.L17_*`, 19 chunks, 374 final states);
* `seven_fam_17`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[8]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_17`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D17
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L17_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_17 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x300d0000050003450000000000000010170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_17).keys = true := by
  rw [finT_17_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x300d0000050003450000000000000010170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin17_0, fin17_1, fin17_2, fin17_3, fin17_4, fin17_5, fin17_6, fin17_7, fin17_8, fin17_9, fin17_10, fin17_11, fin17_12, fin17_13, fin17_14, fin17_15, fin17_16, fin17_17, fin17_18, fin17_19] ++ ([fin17_20, fin17_21, fin17_22, fin17_23, fin17_24, fin17_25, fin17_26, fin17_27, fin17_28, fin17_29, fin17_30, fin17_31, fin17_32, fin17_33, fin17_34, fin17_35, fin17_36, fin17_37, fin17_38, fin17_39] ++ ([fin17_40, fin17_41, fin17_42, fin17_43, fin17_44, fin17_45, fin17_46, fin17_47, fin17_48, fin17_49, fin17_50, fin17_51, fin17_52, fin17_53, fin17_54, fin17_55, fin17_56, fin17_57, fin17_58, fin17_59] ++ ([fin17_60, fin17_61, fin17_62, fin17_63, fin17_64, fin17_65, fin17_66, fin17_67, fin17_68, fin17_69, fin17_70, fin17_71, fin17_72, fin17_73, fin17_74, fin17_75, fin17_76, fin17_77, fin17_78, fin17_79] ++ ([fin17_80, fin17_81, fin17_82, fin17_83, fin17_84, fin17_85, fin17_86, fin17_87, fin17_88, fin17_89, fin17_90, fin17_91, fin17_92, fin17_93, fin17_94, fin17_95, fin17_96, fin17_97, fin17_98, fin17_99] ++ ([fin17_100, fin17_101, fin17_102, fin17_103, fin17_104, fin17_105, fin17_106, fin17_107, fin17_108, fin17_109, fin17_110, fin17_111, fin17_112, fin17_113, fin17_114, fin17_115, fin17_116, fin17_117, fin17_118, fin17_119] ++ ([fin17_120, fin17_121, fin17_122, fin17_123, fin17_124, fin17_125, fin17_126, fin17_127, fin17_128, fin17_129, fin17_130, fin17_131, fin17_132, fin17_133, fin17_134, fin17_135, fin17_136, fin17_137, fin17_138, fin17_139] ++ ([fin17_140, fin17_141, fin17_142, fin17_143, fin17_144, fin17_145, fin17_146, fin17_147, fin17_148, fin17_149, fin17_150, fin17_151, fin17_152, fin17_153, fin17_154, fin17_155, fin17_156, fin17_157, fin17_158, fin17_159] ++ ([fin17_160, fin17_161, fin17_162, fin17_163, fin17_164, fin17_165, fin17_166, fin17_167, fin17_168, fin17_169, fin17_170, fin17_171, fin17_172, fin17_173, fin17_174, fin17_175, fin17_176, fin17_177, fin17_178, fin17_179] ++ ([fin17_180, fin17_181, fin17_182, fin17_183, fin17_184, fin17_185, fin17_186, fin17_187, fin17_188, fin17_189, fin17_190, fin17_191, fin17_192, fin17_193, fin17_194, fin17_195, fin17_196, fin17_197, fin17_198, fin17_199] ++ ([fin17_200, fin17_201, fin17_202, fin17_203, fin17_204, fin17_205, fin17_206, fin17_207, fin17_208, fin17_209, fin17_210, fin17_211, fin17_212, fin17_213, fin17_214, fin17_215, fin17_216, fin17_217, fin17_218, fin17_219] ++ ([fin17_220, fin17_221, fin17_222, fin17_223, fin17_224, fin17_225, fin17_226, fin17_227, fin17_228, fin17_229, fin17_230, fin17_231, fin17_232, fin17_233, fin17_234, fin17_235, fin17_236, fin17_237, fin17_238, fin17_239] ++ ([fin17_240, fin17_241, fin17_242, fin17_243, fin17_244, fin17_245, fin17_246, fin17_247, fin17_248, fin17_249, fin17_250, fin17_251, fin17_252, fin17_253, fin17_254, fin17_255, fin17_256, fin17_257, fin17_258, fin17_259] ++ ([fin17_260, fin17_261, fin17_262, fin17_263, fin17_264, fin17_265, fin17_266, fin17_267, fin17_268, fin17_269, fin17_270, fin17_271, fin17_272, fin17_273, fin17_274, fin17_275, fin17_276, fin17_277, fin17_278, fin17_279] ++ ([fin17_280, fin17_281, fin17_282, fin17_283, fin17_284, fin17_285, fin17_286, fin17_287, fin17_288, fin17_289, fin17_290, fin17_291, fin17_292, fin17_293, fin17_294, fin17_295, fin17_296, fin17_297, fin17_298, fin17_299] ++ ([fin17_300, fin17_301, fin17_302, fin17_303, fin17_304, fin17_305, fin17_306, fin17_307, fin17_308, fin17_309, fin17_310, fin17_311, fin17_312, fin17_313, fin17_314, fin17_315, fin17_316, fin17_317, fin17_318, fin17_319] ++ ([fin17_320, fin17_321, fin17_322, fin17_323, fin17_324, fin17_325, fin17_326, fin17_327, fin17_328, fin17_329, fin17_330, fin17_331, fin17_332, fin17_333, fin17_334, fin17_335, fin17_336, fin17_337, fin17_338, fin17_339] ++ ([fin17_340, fin17_341, fin17_342, fin17_343, fin17_344, fin17_345, fin17_346, fin17_347, fin17_348, fin17_349, fin17_350, fin17_351, fin17_352, fin17_353, fin17_354, fin17_355, fin17_356, fin17_357, fin17_358, fin17_359] ++ ([fin17_360, fin17_361, fin17_362, fin17_363, fin17_364, fin17_365, fin17_366, fin17_367, fin17_368, fin17_369, fin17_370, fin17_371, fin17_372, fin17_373]))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_17_0, Bool.true_and, allNat_append', seven_leaf_17_1, Bool.true_and, allNat_append', seven_leaf_17_2, Bool.true_and, allNat_append', seven_leaf_17_3, Bool.true_and, allNat_append', seven_leaf_17_4, Bool.true_and, allNat_append', seven_leaf_17_5, Bool.true_and, allNat_append', seven_leaf_17_6, Bool.true_and, allNat_append', seven_leaf_17_7, Bool.true_and, allNat_append', seven_leaf_17_8, Bool.true_and, allNat_append', seven_leaf_17_9, Bool.true_and, allNat_append', seven_leaf_17_10, Bool.true_and, allNat_append', seven_leaf_17_11, Bool.true_and, allNat_append', seven_leaf_17_12, Bool.true_and, allNat_append', seven_leaf_17_13, Bool.true_and, allNat_append', seven_leaf_17_14, Bool.true_and, allNat_append', seven_leaf_17_15, Bool.true_and, allNat_append', seven_leaf_17_16, Bool.true_and, allNat_append', seven_leaf_17_17, Bool.true_and]
  exact seven_leaf_17_18

theorem seven_fam_17 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 8 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x300d0000050003450000000000000010170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 8 0 := seed7_17
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_17 ord7_17_perm (nat_lit 0x300d0000050003450000000000000010170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_17 (by rw [← fam7_17_eq]; exact seven_dfs_17) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_17 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
