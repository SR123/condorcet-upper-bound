/-
CDCert.K6.Seven.S19 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 19**
(seed type 10, top slice T_6).

* `seven_leaves_19`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_19_k` of `CDCert.K6.Seven.L19_*`, 18 chunks, 358 final states);
* `seven_fam_19`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[10]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_19`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D19
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L19_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_19 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0xc3d304001300000000000000000000000000000000000000000000000000004dc3300d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_19).keys = true := by
  rw [finT_19_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0xc3d304001300000000000000000000000000000000000000000000000000004dc3300d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin19_0, fin19_1, fin19_2, fin19_3, fin19_4, fin19_5, fin19_6, fin19_7, fin19_8, fin19_9, fin19_10, fin19_11, fin19_12, fin19_13, fin19_14, fin19_15, fin19_16, fin19_17, fin19_18, fin19_19] ++ ([fin19_20, fin19_21, fin19_22, fin19_23, fin19_24, fin19_25, fin19_26, fin19_27, fin19_28, fin19_29, fin19_30, fin19_31, fin19_32, fin19_33, fin19_34, fin19_35, fin19_36, fin19_37, fin19_38, fin19_39] ++ ([fin19_40, fin19_41, fin19_42, fin19_43, fin19_44, fin19_45, fin19_46, fin19_47, fin19_48, fin19_49, fin19_50, fin19_51, fin19_52, fin19_53, fin19_54, fin19_55, fin19_56, fin19_57, fin19_58, fin19_59] ++ ([fin19_60, fin19_61, fin19_62, fin19_63, fin19_64, fin19_65, fin19_66, fin19_67, fin19_68, fin19_69, fin19_70, fin19_71, fin19_72, fin19_73, fin19_74, fin19_75, fin19_76, fin19_77, fin19_78, fin19_79] ++ ([fin19_80, fin19_81, fin19_82, fin19_83, fin19_84, fin19_85, fin19_86, fin19_87, fin19_88, fin19_89, fin19_90, fin19_91, fin19_92, fin19_93, fin19_94, fin19_95, fin19_96, fin19_97, fin19_98, fin19_99] ++ ([fin19_100, fin19_101, fin19_102, fin19_103, fin19_104, fin19_105, fin19_106, fin19_107, fin19_108, fin19_109, fin19_110, fin19_111, fin19_112, fin19_113, fin19_114, fin19_115, fin19_116, fin19_117, fin19_118, fin19_119] ++ ([fin19_120, fin19_121, fin19_122, fin19_123, fin19_124, fin19_125, fin19_126, fin19_127, fin19_128, fin19_129, fin19_130, fin19_131, fin19_132, fin19_133, fin19_134, fin19_135, fin19_136, fin19_137, fin19_138, fin19_139] ++ ([fin19_140, fin19_141, fin19_142, fin19_143, fin19_144, fin19_145, fin19_146, fin19_147, fin19_148, fin19_149, fin19_150, fin19_151, fin19_152, fin19_153, fin19_154, fin19_155, fin19_156, fin19_157, fin19_158, fin19_159] ++ ([fin19_160, fin19_161, fin19_162, fin19_163, fin19_164, fin19_165, fin19_166, fin19_167, fin19_168, fin19_169, fin19_170, fin19_171, fin19_172, fin19_173, fin19_174, fin19_175, fin19_176, fin19_177, fin19_178, fin19_179] ++ ([fin19_180, fin19_181, fin19_182, fin19_183, fin19_184, fin19_185, fin19_186, fin19_187, fin19_188, fin19_189, fin19_190, fin19_191, fin19_192, fin19_193, fin19_194, fin19_195, fin19_196, fin19_197, fin19_198, fin19_199] ++ ([fin19_200, fin19_201, fin19_202, fin19_203, fin19_204, fin19_205, fin19_206, fin19_207, fin19_208, fin19_209, fin19_210, fin19_211, fin19_212, fin19_213, fin19_214, fin19_215, fin19_216, fin19_217, fin19_218, fin19_219] ++ ([fin19_220, fin19_221, fin19_222, fin19_223, fin19_224, fin19_225, fin19_226, fin19_227, fin19_228, fin19_229, fin19_230, fin19_231, fin19_232, fin19_233, fin19_234, fin19_235, fin19_236, fin19_237, fin19_238, fin19_239] ++ ([fin19_240, fin19_241, fin19_242, fin19_243, fin19_244, fin19_245, fin19_246, fin19_247, fin19_248, fin19_249, fin19_250, fin19_251, fin19_252, fin19_253, fin19_254, fin19_255, fin19_256, fin19_257, fin19_258, fin19_259] ++ ([fin19_260, fin19_261, fin19_262, fin19_263, fin19_264, fin19_265, fin19_266, fin19_267, fin19_268, fin19_269, fin19_270, fin19_271, fin19_272, fin19_273, fin19_274, fin19_275, fin19_276, fin19_277, fin19_278, fin19_279] ++ ([fin19_280, fin19_281, fin19_282, fin19_283, fin19_284, fin19_285, fin19_286, fin19_287, fin19_288, fin19_289, fin19_290, fin19_291, fin19_292, fin19_293, fin19_294, fin19_295, fin19_296, fin19_297, fin19_298, fin19_299] ++ ([fin19_300, fin19_301, fin19_302, fin19_303, fin19_304, fin19_305, fin19_306, fin19_307, fin19_308, fin19_309, fin19_310, fin19_311, fin19_312, fin19_313, fin19_314, fin19_315, fin19_316, fin19_317, fin19_318, fin19_319] ++ ([fin19_320, fin19_321, fin19_322, fin19_323, fin19_324, fin19_325, fin19_326, fin19_327, fin19_328, fin19_329, fin19_330, fin19_331, fin19_332, fin19_333, fin19_334, fin19_335, fin19_336, fin19_337, fin19_338, fin19_339] ++ ([fin19_340, fin19_341, fin19_342, fin19_343, fin19_344, fin19_345, fin19_346, fin19_347, fin19_348, fin19_349, fin19_350, fin19_351, fin19_352, fin19_353, fin19_354, fin19_355, fin19_356, fin19_357])))))))))))))))))) = true
  rw [allNat_append', seven_leaf_19_0, Bool.true_and, allNat_append', seven_leaf_19_1, Bool.true_and, allNat_append', seven_leaf_19_2, Bool.true_and, allNat_append', seven_leaf_19_3, Bool.true_and, allNat_append', seven_leaf_19_4, Bool.true_and, allNat_append', seven_leaf_19_5, Bool.true_and, allNat_append', seven_leaf_19_6, Bool.true_and, allNat_append', seven_leaf_19_7, Bool.true_and, allNat_append', seven_leaf_19_8, Bool.true_and, allNat_append', seven_leaf_19_9, Bool.true_and, allNat_append', seven_leaf_19_10, Bool.true_and, allNat_append', seven_leaf_19_11, Bool.true_and, allNat_append', seven_leaf_19_12, Bool.true_and, allNat_append', seven_leaf_19_13, Bool.true_and, allNat_append', seven_leaf_19_14, Bool.true_and, allNat_append', seven_leaf_19_15, Bool.true_and, allNat_append', seven_leaf_19_16, Bool.true_and]
  exact seven_leaf_19_17

theorem seven_fam_19 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 10 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0xc3d304001300000000000000000000000000000000000000000000000000004dc3300d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 10 0 := seed7_19
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_19 ord7_19_perm (nat_lit 0xc3d304001300000000000000000000000000000000000000000000000000004dc3300d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_19 (by rw [← fam7_19_eq]; exact seven_dfs_19) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_19 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
