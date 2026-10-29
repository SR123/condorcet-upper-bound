/-
CDCert.K6.Seven.S24 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 24**
(seed type 13, bottom slice B_6).

* `seven_leaves_24`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_24_k` of `CDCert.K6.Seven.L24_*`, 19 chunks, 366 final states);
* `seven_fam_24`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[13]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_24`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D24
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L24_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_24 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_24).keys = true := by
  rw [finT_24_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin24_0, fin24_1, fin24_2, fin24_3, fin24_4, fin24_5, fin24_6, fin24_7, fin24_8, fin24_9, fin24_10, fin24_11, fin24_12, fin24_13, fin24_14, fin24_15, fin24_16, fin24_17, fin24_18, fin24_19] ++ ([fin24_20, fin24_21, fin24_22, fin24_23, fin24_24, fin24_25, fin24_26, fin24_27, fin24_28, fin24_29, fin24_30, fin24_31, fin24_32, fin24_33, fin24_34, fin24_35, fin24_36, fin24_37, fin24_38, fin24_39] ++ ([fin24_40, fin24_41, fin24_42, fin24_43, fin24_44, fin24_45, fin24_46, fin24_47, fin24_48, fin24_49, fin24_50, fin24_51, fin24_52, fin24_53, fin24_54, fin24_55, fin24_56, fin24_57, fin24_58, fin24_59] ++ ([fin24_60, fin24_61, fin24_62, fin24_63, fin24_64, fin24_65, fin24_66, fin24_67, fin24_68, fin24_69, fin24_70, fin24_71, fin24_72, fin24_73, fin24_74, fin24_75, fin24_76, fin24_77, fin24_78, fin24_79] ++ ([fin24_80, fin24_81, fin24_82, fin24_83, fin24_84, fin24_85, fin24_86, fin24_87, fin24_88, fin24_89, fin24_90, fin24_91, fin24_92, fin24_93, fin24_94, fin24_95, fin24_96, fin24_97, fin24_98, fin24_99] ++ ([fin24_100, fin24_101, fin24_102, fin24_103, fin24_104, fin24_105, fin24_106, fin24_107, fin24_108, fin24_109, fin24_110, fin24_111, fin24_112, fin24_113, fin24_114, fin24_115, fin24_116, fin24_117, fin24_118, fin24_119] ++ ([fin24_120, fin24_121, fin24_122, fin24_123, fin24_124, fin24_125, fin24_126, fin24_127, fin24_128, fin24_129, fin24_130, fin24_131, fin24_132, fin24_133, fin24_134, fin24_135, fin24_136, fin24_137, fin24_138, fin24_139] ++ ([fin24_140, fin24_141, fin24_142, fin24_143, fin24_144, fin24_145, fin24_146, fin24_147, fin24_148, fin24_149, fin24_150, fin24_151, fin24_152, fin24_153, fin24_154, fin24_155, fin24_156, fin24_157, fin24_158, fin24_159] ++ ([fin24_160, fin24_161, fin24_162, fin24_163, fin24_164, fin24_165, fin24_166, fin24_167, fin24_168, fin24_169, fin24_170, fin24_171, fin24_172, fin24_173, fin24_174, fin24_175, fin24_176, fin24_177, fin24_178, fin24_179] ++ ([fin24_180, fin24_181, fin24_182, fin24_183, fin24_184, fin24_185, fin24_186, fin24_187, fin24_188, fin24_189, fin24_190, fin24_191, fin24_192, fin24_193, fin24_194, fin24_195, fin24_196, fin24_197, fin24_198, fin24_199] ++ ([fin24_200, fin24_201, fin24_202, fin24_203, fin24_204, fin24_205, fin24_206, fin24_207, fin24_208, fin24_209, fin24_210, fin24_211, fin24_212, fin24_213, fin24_214, fin24_215, fin24_216, fin24_217, fin24_218, fin24_219] ++ ([fin24_220, fin24_221, fin24_222, fin24_223, fin24_224, fin24_225, fin24_226, fin24_227, fin24_228, fin24_229, fin24_230, fin24_231, fin24_232, fin24_233, fin24_234, fin24_235, fin24_236, fin24_237, fin24_238, fin24_239] ++ ([fin24_240, fin24_241, fin24_242, fin24_243, fin24_244, fin24_245, fin24_246, fin24_247, fin24_248, fin24_249, fin24_250, fin24_251, fin24_252, fin24_253, fin24_254, fin24_255, fin24_256, fin24_257, fin24_258, fin24_259] ++ ([fin24_260, fin24_261, fin24_262, fin24_263, fin24_264, fin24_265, fin24_266, fin24_267, fin24_268, fin24_269, fin24_270, fin24_271, fin24_272, fin24_273, fin24_274, fin24_275, fin24_276, fin24_277, fin24_278, fin24_279] ++ ([fin24_280, fin24_281, fin24_282, fin24_283, fin24_284, fin24_285, fin24_286, fin24_287, fin24_288, fin24_289, fin24_290, fin24_291, fin24_292, fin24_293, fin24_294, fin24_295, fin24_296, fin24_297, fin24_298, fin24_299] ++ ([fin24_300, fin24_301, fin24_302, fin24_303, fin24_304, fin24_305, fin24_306, fin24_307, fin24_308, fin24_309, fin24_310, fin24_311, fin24_312, fin24_313, fin24_314, fin24_315, fin24_316, fin24_317, fin24_318, fin24_319] ++ ([fin24_320, fin24_321, fin24_322, fin24_323, fin24_324, fin24_325, fin24_326, fin24_327, fin24_328, fin24_329, fin24_330, fin24_331, fin24_332, fin24_333, fin24_334, fin24_335, fin24_336, fin24_337, fin24_338, fin24_339] ++ ([fin24_340, fin24_341, fin24_342, fin24_343, fin24_344, fin24_345, fin24_346, fin24_347, fin24_348, fin24_349, fin24_350, fin24_351, fin24_352, fin24_353, fin24_354, fin24_355, fin24_356, fin24_357, fin24_358, fin24_359] ++ ([fin24_360, fin24_361, fin24_362, fin24_363, fin24_364, fin24_365]))))))))))))))))))) = true
  rw [allNat_append', seven_leaf_24_0, Bool.true_and, allNat_append', seven_leaf_24_1, Bool.true_and, allNat_append', seven_leaf_24_2, Bool.true_and, allNat_append', seven_leaf_24_3, Bool.true_and, allNat_append', seven_leaf_24_4, Bool.true_and, allNat_append', seven_leaf_24_5, Bool.true_and, allNat_append', seven_leaf_24_6, Bool.true_and, allNat_append', seven_leaf_24_7, Bool.true_and, allNat_append', seven_leaf_24_8, Bool.true_and, allNat_append', seven_leaf_24_9, Bool.true_and, allNat_append', seven_leaf_24_10, Bool.true_and, allNat_append', seven_leaf_24_11, Bool.true_and, allNat_append', seven_leaf_24_12, Bool.true_and, allNat_append', seven_leaf_24_13, Bool.true_and, allNat_append', seven_leaf_24_14, Bool.true_and, allNat_append', seven_leaf_24_15, Bool.true_and, allNat_append', seven_leaf_24_16, Bool.true_and, allNat_append', seven_leaf_24_17, Bool.true_and]
  exact seven_leaf_24_18

theorem seven_fam_24 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 13 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 13 0 := seed7_24
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_24 ord7_24_perm (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_24 (by rw [← fam7_24_eq]; exact seven_dfs_24) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_24 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
