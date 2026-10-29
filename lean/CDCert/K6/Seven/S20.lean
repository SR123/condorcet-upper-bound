/-
CDCert.K6.Seven.S20 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 20**
(seed type 11, bottom slice B_6).

* `seven_leaves_20`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_20_k` of `CDCert.K6.Seven.L20_*`, 18 chunks, 344 final states);
* `seven_fam_20`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[11]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_20`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D20
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L20_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_20 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_20).keys = true := by
  rw [finT_20_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x34cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin20_0, fin20_1, fin20_2, fin20_3, fin20_4, fin20_5, fin20_6, fin20_7, fin20_8, fin20_9, fin20_10, fin20_11, fin20_12, fin20_13, fin20_14, fin20_15, fin20_16, fin20_17, fin20_18, fin20_19] ++ ([fin20_20, fin20_21, fin20_22, fin20_23, fin20_24, fin20_25, fin20_26, fin20_27, fin20_28, fin20_29, fin20_30, fin20_31, fin20_32, fin20_33, fin20_34, fin20_35, fin20_36, fin20_37, fin20_38, fin20_39] ++ ([fin20_40, fin20_41, fin20_42, fin20_43, fin20_44, fin20_45, fin20_46, fin20_47, fin20_48, fin20_49, fin20_50, fin20_51, fin20_52, fin20_53, fin20_54, fin20_55, fin20_56, fin20_57, fin20_58, fin20_59] ++ ([fin20_60, fin20_61, fin20_62, fin20_63, fin20_64, fin20_65, fin20_66, fin20_67, fin20_68, fin20_69, fin20_70, fin20_71, fin20_72, fin20_73, fin20_74, fin20_75, fin20_76, fin20_77, fin20_78, fin20_79] ++ ([fin20_80, fin20_81, fin20_82, fin20_83, fin20_84, fin20_85, fin20_86, fin20_87, fin20_88, fin20_89, fin20_90, fin20_91, fin20_92, fin20_93, fin20_94, fin20_95, fin20_96, fin20_97, fin20_98, fin20_99] ++ ([fin20_100, fin20_101, fin20_102, fin20_103, fin20_104, fin20_105, fin20_106, fin20_107, fin20_108, fin20_109, fin20_110, fin20_111, fin20_112, fin20_113, fin20_114, fin20_115, fin20_116, fin20_117, fin20_118, fin20_119] ++ ([fin20_120, fin20_121, fin20_122, fin20_123, fin20_124, fin20_125, fin20_126, fin20_127, fin20_128, fin20_129, fin20_130, fin20_131, fin20_132, fin20_133, fin20_134, fin20_135, fin20_136, fin20_137, fin20_138, fin20_139] ++ ([fin20_140, fin20_141, fin20_142, fin20_143, fin20_144, fin20_145, fin20_146, fin20_147, fin20_148, fin20_149, fin20_150, fin20_151, fin20_152, fin20_153, fin20_154, fin20_155, fin20_156, fin20_157, fin20_158, fin20_159] ++ ([fin20_160, fin20_161, fin20_162, fin20_163, fin20_164, fin20_165, fin20_166, fin20_167, fin20_168, fin20_169, fin20_170, fin20_171, fin20_172, fin20_173, fin20_174, fin20_175, fin20_176, fin20_177, fin20_178, fin20_179] ++ ([fin20_180, fin20_181, fin20_182, fin20_183, fin20_184, fin20_185, fin20_186, fin20_187, fin20_188, fin20_189, fin20_190, fin20_191, fin20_192, fin20_193, fin20_194, fin20_195, fin20_196, fin20_197, fin20_198, fin20_199] ++ ([fin20_200, fin20_201, fin20_202, fin20_203, fin20_204, fin20_205, fin20_206, fin20_207, fin20_208, fin20_209, fin20_210, fin20_211, fin20_212, fin20_213, fin20_214, fin20_215, fin20_216, fin20_217, fin20_218, fin20_219] ++ ([fin20_220, fin20_221, fin20_222, fin20_223, fin20_224, fin20_225, fin20_226, fin20_227, fin20_228, fin20_229, fin20_230, fin20_231, fin20_232, fin20_233, fin20_234, fin20_235, fin20_236, fin20_237, fin20_238, fin20_239] ++ ([fin20_240, fin20_241, fin20_242, fin20_243, fin20_244, fin20_245, fin20_246, fin20_247, fin20_248, fin20_249, fin20_250, fin20_251, fin20_252, fin20_253, fin20_254, fin20_255, fin20_256, fin20_257, fin20_258, fin20_259] ++ ([fin20_260, fin20_261, fin20_262, fin20_263, fin20_264, fin20_265, fin20_266, fin20_267, fin20_268, fin20_269, fin20_270, fin20_271, fin20_272, fin20_273, fin20_274, fin20_275, fin20_276, fin20_277, fin20_278, fin20_279] ++ ([fin20_280, fin20_281, fin20_282, fin20_283, fin20_284, fin20_285, fin20_286, fin20_287, fin20_288, fin20_289, fin20_290, fin20_291, fin20_292, fin20_293, fin20_294, fin20_295, fin20_296, fin20_297, fin20_298, fin20_299] ++ ([fin20_300, fin20_301, fin20_302, fin20_303, fin20_304, fin20_305, fin20_306, fin20_307, fin20_308, fin20_309, fin20_310, fin20_311, fin20_312, fin20_313, fin20_314, fin20_315, fin20_316, fin20_317, fin20_318, fin20_319] ++ ([fin20_320, fin20_321, fin20_322, fin20_323, fin20_324, fin20_325, fin20_326, fin20_327, fin20_328, fin20_329, fin20_330, fin20_331, fin20_332, fin20_333, fin20_334, fin20_335, fin20_336, fin20_337, fin20_338, fin20_339] ++ ([fin20_340, fin20_341, fin20_342, fin20_343])))))))))))))))))) = true
  rw [allNat_append', seven_leaf_20_0, Bool.true_and, allNat_append', seven_leaf_20_1, Bool.true_and, allNat_append', seven_leaf_20_2, Bool.true_and, allNat_append', seven_leaf_20_3, Bool.true_and, allNat_append', seven_leaf_20_4, Bool.true_and, allNat_append', seven_leaf_20_5, Bool.true_and, allNat_append', seven_leaf_20_6, Bool.true_and, allNat_append', seven_leaf_20_7, Bool.true_and, allNat_append', seven_leaf_20_8, Bool.true_and, allNat_append', seven_leaf_20_9, Bool.true_and, allNat_append', seven_leaf_20_10, Bool.true_and, allNat_append', seven_leaf_20_11, Bool.true_and, allNat_append', seven_leaf_20_12, Bool.true_and, allNat_append', seven_leaf_20_13, Bool.true_and, allNat_append', seven_leaf_20_14, Bool.true_and, allNat_append', seven_leaf_20_15, Bool.true_and, allNat_append', seven_leaf_20_16, Bool.true_and]
  exact seven_leaf_20_17

theorem seven_fam_20 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 11 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x34cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 11 0 := seed7_20
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_20 ord7_20_perm (nat_lit 0x34cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_20 (by rw [← fam7_20_eq]; exact seven_dfs_20) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_20 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
