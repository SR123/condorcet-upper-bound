/-
CDCert.K6.Seven.S22 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 22**
(seed type 12, bottom slice B_6).

* `seven_leaves_22`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_22_k` of `CDCert.K6.Seven.L22_*`, 18 chunks, 345 final states);
* `seven_fam_22`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[12]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_22`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D22
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L22_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_22 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_22).keys = true := by
  rw [finT_22_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin22_0, fin22_1, fin22_2, fin22_3, fin22_4, fin22_5, fin22_6, fin22_7, fin22_8, fin22_9, fin22_10, fin22_11, fin22_12, fin22_13, fin22_14, fin22_15, fin22_16, fin22_17, fin22_18, fin22_19] ++ ([fin22_20, fin22_21, fin22_22, fin22_23, fin22_24, fin22_25, fin22_26, fin22_27, fin22_28, fin22_29, fin22_30, fin22_31, fin22_32, fin22_33, fin22_34, fin22_35, fin22_36, fin22_37, fin22_38, fin22_39] ++ ([fin22_40, fin22_41, fin22_42, fin22_43, fin22_44, fin22_45, fin22_46, fin22_47, fin22_48, fin22_49, fin22_50, fin22_51, fin22_52, fin22_53, fin22_54, fin22_55, fin22_56, fin22_57, fin22_58, fin22_59] ++ ([fin22_60, fin22_61, fin22_62, fin22_63, fin22_64, fin22_65, fin22_66, fin22_67, fin22_68, fin22_69, fin22_70, fin22_71, fin22_72, fin22_73, fin22_74, fin22_75, fin22_76, fin22_77, fin22_78, fin22_79] ++ ([fin22_80, fin22_81, fin22_82, fin22_83, fin22_84, fin22_85, fin22_86, fin22_87, fin22_88, fin22_89, fin22_90, fin22_91, fin22_92, fin22_93, fin22_94, fin22_95, fin22_96, fin22_97, fin22_98, fin22_99] ++ ([fin22_100, fin22_101, fin22_102, fin22_103, fin22_104, fin22_105, fin22_106, fin22_107, fin22_108, fin22_109, fin22_110, fin22_111, fin22_112, fin22_113, fin22_114, fin22_115, fin22_116, fin22_117, fin22_118, fin22_119] ++ ([fin22_120, fin22_121, fin22_122, fin22_123, fin22_124, fin22_125, fin22_126, fin22_127, fin22_128, fin22_129, fin22_130, fin22_131, fin22_132, fin22_133, fin22_134, fin22_135, fin22_136, fin22_137, fin22_138, fin22_139] ++ ([fin22_140, fin22_141, fin22_142, fin22_143, fin22_144, fin22_145, fin22_146, fin22_147, fin22_148, fin22_149, fin22_150, fin22_151, fin22_152, fin22_153, fin22_154, fin22_155, fin22_156, fin22_157, fin22_158, fin22_159] ++ ([fin22_160, fin22_161, fin22_162, fin22_163, fin22_164, fin22_165, fin22_166, fin22_167, fin22_168, fin22_169, fin22_170, fin22_171, fin22_172, fin22_173, fin22_174, fin22_175, fin22_176, fin22_177, fin22_178, fin22_179] ++ ([fin22_180, fin22_181, fin22_182, fin22_183, fin22_184, fin22_185, fin22_186, fin22_187, fin22_188, fin22_189, fin22_190, fin22_191, fin22_192, fin22_193, fin22_194, fin22_195, fin22_196, fin22_197, fin22_198, fin22_199] ++ ([fin22_200, fin22_201, fin22_202, fin22_203, fin22_204, fin22_205, fin22_206, fin22_207, fin22_208, fin22_209, fin22_210, fin22_211, fin22_212, fin22_213, fin22_214, fin22_215, fin22_216, fin22_217, fin22_218, fin22_219] ++ ([fin22_220, fin22_221, fin22_222, fin22_223, fin22_224, fin22_225, fin22_226, fin22_227, fin22_228, fin22_229, fin22_230, fin22_231, fin22_232, fin22_233, fin22_234, fin22_235, fin22_236, fin22_237, fin22_238, fin22_239] ++ ([fin22_240, fin22_241, fin22_242, fin22_243, fin22_244, fin22_245, fin22_246, fin22_247, fin22_248, fin22_249, fin22_250, fin22_251, fin22_252, fin22_253, fin22_254, fin22_255, fin22_256, fin22_257, fin22_258, fin22_259] ++ ([fin22_260, fin22_261, fin22_262, fin22_263, fin22_264, fin22_265, fin22_266, fin22_267, fin22_268, fin22_269, fin22_270, fin22_271, fin22_272, fin22_273, fin22_274, fin22_275, fin22_276, fin22_277, fin22_278, fin22_279] ++ ([fin22_280, fin22_281, fin22_282, fin22_283, fin22_284, fin22_285, fin22_286, fin22_287, fin22_288, fin22_289, fin22_290, fin22_291, fin22_292, fin22_293, fin22_294, fin22_295, fin22_296, fin22_297, fin22_298, fin22_299] ++ ([fin22_300, fin22_301, fin22_302, fin22_303, fin22_304, fin22_305, fin22_306, fin22_307, fin22_308, fin22_309, fin22_310, fin22_311, fin22_312, fin22_313, fin22_314, fin22_315, fin22_316, fin22_317, fin22_318, fin22_319] ++ ([fin22_320, fin22_321, fin22_322, fin22_323, fin22_324, fin22_325, fin22_326, fin22_327, fin22_328, fin22_329, fin22_330, fin22_331, fin22_332, fin22_333, fin22_334, fin22_335, fin22_336, fin22_337, fin22_338, fin22_339] ++ ([fin22_340, fin22_341, fin22_342, fin22_343, fin22_344])))))))))))))))))) = true
  rw [allNat_append', seven_leaf_22_0, Bool.true_and, allNat_append', seven_leaf_22_1, Bool.true_and, allNat_append', seven_leaf_22_2, Bool.true_and, allNat_append', seven_leaf_22_3, Bool.true_and, allNat_append', seven_leaf_22_4, Bool.true_and, allNat_append', seven_leaf_22_5, Bool.true_and, allNat_append', seven_leaf_22_6, Bool.true_and, allNat_append', seven_leaf_22_7, Bool.true_and, allNat_append', seven_leaf_22_8, Bool.true_and, allNat_append', seven_leaf_22_9, Bool.true_and, allNat_append', seven_leaf_22_10, Bool.true_and, allNat_append', seven_leaf_22_11, Bool.true_and, allNat_append', seven_leaf_22_12, Bool.true_and, allNat_append', seven_leaf_22_13, Bool.true_and, allNat_append', seven_leaf_22_14, Bool.true_and, allNat_append', seven_leaf_22_15, Bool.true_and, allNat_append', seven_leaf_22_16, Bool.true_and]
  exact seven_leaf_22_17

theorem seven_fam_22 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 12 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 12 0 := seed7_22
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_22 ord7_22_perm (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_22 (by rw [← fam7_22_eq]; exact seven_dfs_22) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_22 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
