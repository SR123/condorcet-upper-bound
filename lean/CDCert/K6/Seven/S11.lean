/-
CDCert.K6.Seven.S11 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 11**
(seed type 5, top slice T_6).

* `seven_leaves_11`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_11_k` of `CDCert.K6.Seven.L11_*`, 18 chunks, 348 final states);
* `seven_fam_11`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[5]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_11`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D11
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L11_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_11 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) (finT_11).keys = true := by
  rw [finT_11_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) ([fin11_0, fin11_1, fin11_2, fin11_3, fin11_4, fin11_5, fin11_6, fin11_7, fin11_8, fin11_9, fin11_10, fin11_11, fin11_12, fin11_13, fin11_14, fin11_15, fin11_16, fin11_17, fin11_18, fin11_19] ++ ([fin11_20, fin11_21, fin11_22, fin11_23, fin11_24, fin11_25, fin11_26, fin11_27, fin11_28, fin11_29, fin11_30, fin11_31, fin11_32, fin11_33, fin11_34, fin11_35, fin11_36, fin11_37, fin11_38, fin11_39] ++ ([fin11_40, fin11_41, fin11_42, fin11_43, fin11_44, fin11_45, fin11_46, fin11_47, fin11_48, fin11_49, fin11_50, fin11_51, fin11_52, fin11_53, fin11_54, fin11_55, fin11_56, fin11_57, fin11_58, fin11_59] ++ ([fin11_60, fin11_61, fin11_62, fin11_63, fin11_64, fin11_65, fin11_66, fin11_67, fin11_68, fin11_69, fin11_70, fin11_71, fin11_72, fin11_73, fin11_74, fin11_75, fin11_76, fin11_77, fin11_78, fin11_79] ++ ([fin11_80, fin11_81, fin11_82, fin11_83, fin11_84, fin11_85, fin11_86, fin11_87, fin11_88, fin11_89, fin11_90, fin11_91, fin11_92, fin11_93, fin11_94, fin11_95, fin11_96, fin11_97, fin11_98, fin11_99] ++ ([fin11_100, fin11_101, fin11_102, fin11_103, fin11_104, fin11_105, fin11_106, fin11_107, fin11_108, fin11_109, fin11_110, fin11_111, fin11_112, fin11_113, fin11_114, fin11_115, fin11_116, fin11_117, fin11_118, fin11_119] ++ ([fin11_120, fin11_121, fin11_122, fin11_123, fin11_124, fin11_125, fin11_126, fin11_127, fin11_128, fin11_129, fin11_130, fin11_131, fin11_132, fin11_133, fin11_134, fin11_135, fin11_136, fin11_137, fin11_138, fin11_139] ++ ([fin11_140, fin11_141, fin11_142, fin11_143, fin11_144, fin11_145, fin11_146, fin11_147, fin11_148, fin11_149, fin11_150, fin11_151, fin11_152, fin11_153, fin11_154, fin11_155, fin11_156, fin11_157, fin11_158, fin11_159] ++ ([fin11_160, fin11_161, fin11_162, fin11_163, fin11_164, fin11_165, fin11_166, fin11_167, fin11_168, fin11_169, fin11_170, fin11_171, fin11_172, fin11_173, fin11_174, fin11_175, fin11_176, fin11_177, fin11_178, fin11_179] ++ ([fin11_180, fin11_181, fin11_182, fin11_183, fin11_184, fin11_185, fin11_186, fin11_187, fin11_188, fin11_189, fin11_190, fin11_191, fin11_192, fin11_193, fin11_194, fin11_195, fin11_196, fin11_197, fin11_198, fin11_199] ++ ([fin11_200, fin11_201, fin11_202, fin11_203, fin11_204, fin11_205, fin11_206, fin11_207, fin11_208, fin11_209, fin11_210, fin11_211, fin11_212, fin11_213, fin11_214, fin11_215, fin11_216, fin11_217, fin11_218, fin11_219] ++ ([fin11_220, fin11_221, fin11_222, fin11_223, fin11_224, fin11_225, fin11_226, fin11_227, fin11_228, fin11_229, fin11_230, fin11_231, fin11_232, fin11_233, fin11_234, fin11_235, fin11_236, fin11_237, fin11_238, fin11_239] ++ ([fin11_240, fin11_241, fin11_242, fin11_243, fin11_244, fin11_245, fin11_246, fin11_247, fin11_248, fin11_249, fin11_250, fin11_251, fin11_252, fin11_253, fin11_254, fin11_255, fin11_256, fin11_257, fin11_258, fin11_259] ++ ([fin11_260, fin11_261, fin11_262, fin11_263, fin11_264, fin11_265, fin11_266, fin11_267, fin11_268, fin11_269, fin11_270, fin11_271, fin11_272, fin11_273, fin11_274, fin11_275, fin11_276, fin11_277, fin11_278, fin11_279] ++ ([fin11_280, fin11_281, fin11_282, fin11_283, fin11_284, fin11_285, fin11_286, fin11_287, fin11_288, fin11_289, fin11_290, fin11_291, fin11_292, fin11_293, fin11_294, fin11_295, fin11_296, fin11_297, fin11_298, fin11_299] ++ ([fin11_300, fin11_301, fin11_302, fin11_303, fin11_304, fin11_305, fin11_306, fin11_307, fin11_308, fin11_309, fin11_310, fin11_311, fin11_312, fin11_313, fin11_314, fin11_315, fin11_316, fin11_317, fin11_318, fin11_319] ++ ([fin11_320, fin11_321, fin11_322, fin11_323, fin11_324, fin11_325, fin11_326, fin11_327, fin11_328, fin11_329, fin11_330, fin11_331, fin11_332, fin11_333, fin11_334, fin11_335, fin11_336, fin11_337, fin11_338, fin11_339] ++ ([fin11_340, fin11_341, fin11_342, fin11_343, fin11_344, fin11_345, fin11_346, fin11_347])))))))))))))))))) = true
  rw [allNat_append', seven_leaf_11_0, Bool.true_and, allNat_append', seven_leaf_11_1, Bool.true_and, allNat_append', seven_leaf_11_2, Bool.true_and, allNat_append', seven_leaf_11_3, Bool.true_and, allNat_append', seven_leaf_11_4, Bool.true_and, allNat_append', seven_leaf_11_5, Bool.true_and, allNat_append', seven_leaf_11_6, Bool.true_and, allNat_append', seven_leaf_11_7, Bool.true_and, allNat_append', seven_leaf_11_8, Bool.true_and, allNat_append', seven_leaf_11_9, Bool.true_and, allNat_append', seven_leaf_11_10, Bool.true_and, allNat_append', seven_leaf_11_11, Bool.true_and, allNat_append', seven_leaf_11_12, Bool.true_and, allNat_append', seven_leaf_11_13, Bool.true_and, allNat_append', seven_leaf_11_14, Bool.true_and, allNat_append', seven_leaf_11_15, Bool.true_and, allNat_append', seven_leaf_11_16, Bool.true_and]
  exact seven_leaf_11_17

theorem seven_fam_11 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 5 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 5 0 := seed7_11
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_11 ord7_11_perm (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_11 (by rw [← fam7_11_eq]; exact seven_dfs_11) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_11 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
