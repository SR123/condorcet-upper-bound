/-
CDCert.K6.Seven.S12 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 12**
(seed type 6, bottom slice B_6).

* `seven_leaves_12`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_12_k` of `CDCert.K6.Seven.L12_*`, 18 chunks, 359 final states);
* `seven_fam_12`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[6]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_12`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D12
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L12_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_12 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0034cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_12).keys = true := by
  rw [finT_12_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0034cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin12_0, fin12_1, fin12_2, fin12_3, fin12_4, fin12_5, fin12_6, fin12_7, fin12_8, fin12_9, fin12_10, fin12_11, fin12_12, fin12_13, fin12_14, fin12_15, fin12_16, fin12_17, fin12_18, fin12_19] ++ ([fin12_20, fin12_21, fin12_22, fin12_23, fin12_24, fin12_25, fin12_26, fin12_27, fin12_28, fin12_29, fin12_30, fin12_31, fin12_32, fin12_33, fin12_34, fin12_35, fin12_36, fin12_37, fin12_38, fin12_39] ++ ([fin12_40, fin12_41, fin12_42, fin12_43, fin12_44, fin12_45, fin12_46, fin12_47, fin12_48, fin12_49, fin12_50, fin12_51, fin12_52, fin12_53, fin12_54, fin12_55, fin12_56, fin12_57, fin12_58, fin12_59] ++ ([fin12_60, fin12_61, fin12_62, fin12_63, fin12_64, fin12_65, fin12_66, fin12_67, fin12_68, fin12_69, fin12_70, fin12_71, fin12_72, fin12_73, fin12_74, fin12_75, fin12_76, fin12_77, fin12_78, fin12_79] ++ ([fin12_80, fin12_81, fin12_82, fin12_83, fin12_84, fin12_85, fin12_86, fin12_87, fin12_88, fin12_89, fin12_90, fin12_91, fin12_92, fin12_93, fin12_94, fin12_95, fin12_96, fin12_97, fin12_98, fin12_99] ++ ([fin12_100, fin12_101, fin12_102, fin12_103, fin12_104, fin12_105, fin12_106, fin12_107, fin12_108, fin12_109, fin12_110, fin12_111, fin12_112, fin12_113, fin12_114, fin12_115, fin12_116, fin12_117, fin12_118, fin12_119] ++ ([fin12_120, fin12_121, fin12_122, fin12_123, fin12_124, fin12_125, fin12_126, fin12_127, fin12_128, fin12_129, fin12_130, fin12_131, fin12_132, fin12_133, fin12_134, fin12_135, fin12_136, fin12_137, fin12_138, fin12_139] ++ ([fin12_140, fin12_141, fin12_142, fin12_143, fin12_144, fin12_145, fin12_146, fin12_147, fin12_148, fin12_149, fin12_150, fin12_151, fin12_152, fin12_153, fin12_154, fin12_155, fin12_156, fin12_157, fin12_158, fin12_159] ++ ([fin12_160, fin12_161, fin12_162, fin12_163, fin12_164, fin12_165, fin12_166, fin12_167, fin12_168, fin12_169, fin12_170, fin12_171, fin12_172, fin12_173, fin12_174, fin12_175, fin12_176, fin12_177, fin12_178, fin12_179] ++ ([fin12_180, fin12_181, fin12_182, fin12_183, fin12_184, fin12_185, fin12_186, fin12_187, fin12_188, fin12_189, fin12_190, fin12_191, fin12_192, fin12_193, fin12_194, fin12_195, fin12_196, fin12_197, fin12_198, fin12_199] ++ ([fin12_200, fin12_201, fin12_202, fin12_203, fin12_204, fin12_205, fin12_206, fin12_207, fin12_208, fin12_209, fin12_210, fin12_211, fin12_212, fin12_213, fin12_214, fin12_215, fin12_216, fin12_217, fin12_218, fin12_219] ++ ([fin12_220, fin12_221, fin12_222, fin12_223, fin12_224, fin12_225, fin12_226, fin12_227, fin12_228, fin12_229, fin12_230, fin12_231, fin12_232, fin12_233, fin12_234, fin12_235, fin12_236, fin12_237, fin12_238, fin12_239] ++ ([fin12_240, fin12_241, fin12_242, fin12_243, fin12_244, fin12_245, fin12_246, fin12_247, fin12_248, fin12_249, fin12_250, fin12_251, fin12_252, fin12_253, fin12_254, fin12_255, fin12_256, fin12_257, fin12_258, fin12_259] ++ ([fin12_260, fin12_261, fin12_262, fin12_263, fin12_264, fin12_265, fin12_266, fin12_267, fin12_268, fin12_269, fin12_270, fin12_271, fin12_272, fin12_273, fin12_274, fin12_275, fin12_276, fin12_277, fin12_278, fin12_279] ++ ([fin12_280, fin12_281, fin12_282, fin12_283, fin12_284, fin12_285, fin12_286, fin12_287, fin12_288, fin12_289, fin12_290, fin12_291, fin12_292, fin12_293, fin12_294, fin12_295, fin12_296, fin12_297, fin12_298, fin12_299] ++ ([fin12_300, fin12_301, fin12_302, fin12_303, fin12_304, fin12_305, fin12_306, fin12_307, fin12_308, fin12_309, fin12_310, fin12_311, fin12_312, fin12_313, fin12_314, fin12_315, fin12_316, fin12_317, fin12_318, fin12_319] ++ ([fin12_320, fin12_321, fin12_322, fin12_323, fin12_324, fin12_325, fin12_326, fin12_327, fin12_328, fin12_329, fin12_330, fin12_331, fin12_332, fin12_333, fin12_334, fin12_335, fin12_336, fin12_337, fin12_338, fin12_339] ++ ([fin12_340, fin12_341, fin12_342, fin12_343, fin12_344, fin12_345, fin12_346, fin12_347, fin12_348, fin12_349, fin12_350, fin12_351, fin12_352, fin12_353, fin12_354, fin12_355, fin12_356, fin12_357, fin12_358])))))))))))))))))) = true
  rw [allNat_append', seven_leaf_12_0, Bool.true_and, allNat_append', seven_leaf_12_1, Bool.true_and, allNat_append', seven_leaf_12_2, Bool.true_and, allNat_append', seven_leaf_12_3, Bool.true_and, allNat_append', seven_leaf_12_4, Bool.true_and, allNat_append', seven_leaf_12_5, Bool.true_and, allNat_append', seven_leaf_12_6, Bool.true_and, allNat_append', seven_leaf_12_7, Bool.true_and, allNat_append', seven_leaf_12_8, Bool.true_and, allNat_append', seven_leaf_12_9, Bool.true_and, allNat_append', seven_leaf_12_10, Bool.true_and, allNat_append', seven_leaf_12_11, Bool.true_and, allNat_append', seven_leaf_12_12, Bool.true_and, allNat_append', seven_leaf_12_13, Bool.true_and, allNat_append', seven_leaf_12_14, Bool.true_and, allNat_append', seven_leaf_12_15, Bool.true_and, allNat_append', seven_leaf_12_16, Bool.true_and]
  exact seven_leaf_12_17

theorem seven_fam_12 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 6 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x34cf0034cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 6 0 := seed7_12
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_12 ord7_12_perm (nat_lit 0x34cf0034cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_12 (by rw [← fam7_12_eq]; exact seven_dfs_12) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_12 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
