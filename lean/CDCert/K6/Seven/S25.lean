/-
CDCert.K6.Seven.S25 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 25**
(seed type 13, top slice T_6).

* `seven_leaves_25`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_25_k` of `CDCert.K6.Seven.L25_*`, 19 chunks, 366 final states);
* `seven_fam_25`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[13]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_25`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D25
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L25_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_25 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_25).keys = true := by
  rw [finT_25_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin25_0, fin25_1, fin25_2, fin25_3, fin25_4, fin25_5, fin25_6, fin25_7, fin25_8, fin25_9, fin25_10, fin25_11, fin25_12, fin25_13, fin25_14, fin25_15, fin25_16, fin25_17, fin25_18, fin25_19] ++ ([fin25_20, fin25_21, fin25_22, fin25_23, fin25_24, fin25_25, fin25_26, fin25_27, fin25_28, fin25_29, fin25_30, fin25_31, fin25_32, fin25_33, fin25_34, fin25_35, fin25_36, fin25_37, fin25_38, fin25_39] ++ ([fin25_40, fin25_41, fin25_42, fin25_43, fin25_44, fin25_45, fin25_46, fin25_47, fin25_48, fin25_49, fin25_50, fin25_51, fin25_52, fin25_53, fin25_54, fin25_55, fin25_56, fin25_57, fin25_58, fin25_59] ++ ([fin25_60, fin25_61, fin25_62, fin25_63, fin25_64, fin25_65, fin25_66, fin25_67, fin25_68, fin25_69, fin25_70, fin25_71, fin25_72, fin25_73, fin25_74, fin25_75, fin25_76, fin25_77, fin25_78, fin25_79] ++ ([fin25_80, fin25_81, fin25_82, fin25_83, fin25_84, fin25_85, fin25_86, fin25_87, fin25_88, fin25_89, fin25_90, fin25_91, fin25_92, fin25_93, fin25_94, fin25_95, fin25_96, fin25_97, fin25_98, fin25_99] ++ ([fin25_100, fin25_101, fin25_102, fin25_103, fin25_104, fin25_105, fin25_106, fin25_107, fin25_108, fin25_109, fin25_110, fin25_111, fin25_112, fin25_113, fin25_114, fin25_115, fin25_116, fin25_117, fin25_118, fin25_119] ++ ([fin25_120, fin25_121, fin25_122, fin25_123, fin25_124, fin25_125, fin25_126, fin25_127, fin25_128, fin25_129, fin25_130, fin25_131, fin25_132, fin25_133, fin25_134, fin25_135, fin25_136, fin25_137, fin25_138, fin25_139] ++ ([fin25_140, fin25_141, fin25_142, fin25_143, fin25_144, fin25_145, fin25_146, fin25_147, fin25_148, fin25_149, fin25_150, fin25_151, fin25_152, fin25_153, fin25_154, fin25_155, fin25_156, fin25_157, fin25_158, fin25_159] ++ ([fin25_160, fin25_161, fin25_162, fin25_163, fin25_164, fin25_165, fin25_166, fin25_167, fin25_168, fin25_169, fin25_170, fin25_171, fin25_172, fin25_173, fin25_174, fin25_175, fin25_176, fin25_177, fin25_178, fin25_179] ++ ([fin25_180, fin25_181, fin25_182, fin25_183, fin25_184, fin25_185, fin25_186, fin25_187, fin25_188, fin25_189, fin25_190, fin25_191, fin25_192, fin25_193, fin25_194, fin25_195, fin25_196, fin25_197, fin25_198, fin25_199] ++ ([fin25_200, fin25_201, fin25_202, fin25_203, fin25_204, fin25_205, fin25_206, fin25_207, fin25_208, fin25_209, fin25_210, fin25_211, fin25_212, fin25_213, fin25_214, fin25_215, fin25_216, fin25_217, fin25_218, fin25_219] ++ ([fin25_220, fin25_221, fin25_222, fin25_223, fin25_224, fin25_225, fin25_226, fin25_227, fin25_228, fin25_229, fin25_230, fin25_231, fin25_232, fin25_233, fin25_234, fin25_235, fin25_236, fin25_237, fin25_238, fin25_239] ++ ([fin25_240, fin25_241, fin25_242, fin25_243, fin25_244, fin25_245, fin25_246, fin25_247, fin25_248, fin25_249, fin25_250, fin25_251, fin25_252, fin25_253, fin25_254, fin25_255, fin25_256, fin25_257, fin25_258, fin25_259] ++ ([fin25_260, fin25_261, fin25_262, fin25_263, fin25_264, fin25_265, fin25_266, fin25_267, fin25_268, fin25_269, fin25_270, fin25_271, fin25_272, fin25_273, fin25_274, fin25_275, fin25_276, fin25_277, fin25_278, fin25_279] ++ ([fin25_280, fin25_281, fin25_282, fin25_283, fin25_284, fin25_285, fin25_286, fin25_287, fin25_288, fin25_289, fin25_290, fin25_291, fin25_292, fin25_293, fin25_294, fin25_295, fin25_296, fin25_297, fin25_298, fin25_299] ++ ([fin25_300, fin25_301, fin25_302, fin25_303, fin25_304, fin25_305, fin25_306, fin25_307, fin25_308, fin25_309, fin25_310, fin25_311, fin25_312, fin25_313, fin25_314, fin25_315, fin25_316, fin25_317, fin25_318, fin25_319] ++ ([fin25_320, fin25_321, fin25_322, fin25_323, fin25_324, fin25_325, fin25_326, fin25_327, fin25_328, fin25_329, fin25_330, fin25_331, fin25_332, fin25_333, fin25_334, fin25_335, fin25_336, fin25_337, fin25_338, fin25_339] ++ ([fin25_340, fin25_341, fin25_342, fin25_343, fin25_344, fin25_345, fin25_346, fin25_347, fin25_348, fin25_349, fin25_350, fin25_351, fin25_352, fin25_353, fin25_354, fin25_355, fin25_356, fin25_357, fin25_358, fin25_359] ++ ([fin25_360, fin25_361, fin25_362, fin25_363, fin25_364, fin25_365]))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_25_0, Bool.true_and, allNat_append', seven_leaf_25_1, Bool.true_and, allNat_append', seven_leaf_25_2, Bool.true_and, allNat_append', seven_leaf_25_3, Bool.true_and, allNat_append', seven_leaf_25_4, Bool.true_and, allNat_append', seven_leaf_25_5, Bool.true_and, allNat_append', seven_leaf_25_6, Bool.true_and, allNat_append', seven_leaf_25_7, Bool.true_and, allNat_append', seven_leaf_25_8, Bool.true_and, allNat_append', seven_leaf_25_9, Bool.true_and, allNat_append', seven_leaf_25_10, Bool.true_and, allNat_append', seven_leaf_25_11, Bool.true_and, allNat_append', seven_leaf_25_12, Bool.true_and, allNat_append', seven_leaf_25_13, Bool.true_and, allNat_append', seven_leaf_25_14, Bool.true_and, allNat_append', seven_leaf_25_15, Bool.true_and, allNat_append', seven_leaf_25_16, Bool.true_and, allNat_append', seven_leaf_25_17, Bool.true_and]
  exact seven_leaf_25_18

theorem seven_fam_25 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 13 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := seed7_25
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_25 ord7_25_perm (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_25 (by rw [← fam7_25_eq]; exact seven_dfs_25) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_25 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
