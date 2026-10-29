/-
CDCert.K6.Seven.S06 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 6**
(seed type 3, bottom slice B_6).

* `seven_leaves_6`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_6_k` of `CDCert.K6.Seven.L06_*`, 16 chunks, 308 final states);
* `seven_fam_6`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[3]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_6`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D06
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L06_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_6 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) (finT_6).keys = true := by
  rw [finT_6_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand1 s))) ([fin6_0, fin6_1, fin6_2, fin6_3, fin6_4, fin6_5, fin6_6, fin6_7, fin6_8, fin6_9, fin6_10, fin6_11, fin6_12, fin6_13, fin6_14, fin6_15, fin6_16, fin6_17, fin6_18, fin6_19] ++ ([fin6_20, fin6_21, fin6_22, fin6_23, fin6_24, fin6_25, fin6_26, fin6_27, fin6_28, fin6_29, fin6_30, fin6_31, fin6_32, fin6_33, fin6_34, fin6_35, fin6_36, fin6_37, fin6_38, fin6_39] ++ ([fin6_40, fin6_41, fin6_42, fin6_43, fin6_44, fin6_45, fin6_46, fin6_47, fin6_48, fin6_49, fin6_50, fin6_51, fin6_52, fin6_53, fin6_54, fin6_55, fin6_56, fin6_57, fin6_58, fin6_59] ++ ([fin6_60, fin6_61, fin6_62, fin6_63, fin6_64, fin6_65, fin6_66, fin6_67, fin6_68, fin6_69, fin6_70, fin6_71, fin6_72, fin6_73, fin6_74, fin6_75, fin6_76, fin6_77, fin6_78, fin6_79] ++ ([fin6_80, fin6_81, fin6_82, fin6_83, fin6_84, fin6_85, fin6_86, fin6_87, fin6_88, fin6_89, fin6_90, fin6_91, fin6_92, fin6_93, fin6_94, fin6_95, fin6_96, fin6_97, fin6_98, fin6_99] ++ ([fin6_100, fin6_101, fin6_102, fin6_103, fin6_104, fin6_105, fin6_106, fin6_107, fin6_108, fin6_109, fin6_110, fin6_111, fin6_112, fin6_113, fin6_114, fin6_115, fin6_116, fin6_117, fin6_118, fin6_119] ++ ([fin6_120, fin6_121, fin6_122, fin6_123, fin6_124, fin6_125, fin6_126, fin6_127, fin6_128, fin6_129, fin6_130, fin6_131, fin6_132, fin6_133, fin6_134, fin6_135, fin6_136, fin6_137, fin6_138, fin6_139] ++ ([fin6_140, fin6_141, fin6_142, fin6_143, fin6_144, fin6_145, fin6_146, fin6_147, fin6_148, fin6_149, fin6_150, fin6_151, fin6_152, fin6_153, fin6_154, fin6_155, fin6_156, fin6_157, fin6_158, fin6_159] ++ ([fin6_160, fin6_161, fin6_162, fin6_163, fin6_164, fin6_165, fin6_166, fin6_167, fin6_168, fin6_169, fin6_170, fin6_171, fin6_172, fin6_173, fin6_174, fin6_175, fin6_176, fin6_177, fin6_178, fin6_179] ++ ([fin6_180, fin6_181, fin6_182, fin6_183, fin6_184, fin6_185, fin6_186, fin6_187, fin6_188, fin6_189, fin6_190, fin6_191, fin6_192, fin6_193, fin6_194, fin6_195, fin6_196, fin6_197, fin6_198, fin6_199] ++ ([fin6_200, fin6_201, fin6_202, fin6_203, fin6_204, fin6_205, fin6_206, fin6_207, fin6_208, fin6_209, fin6_210, fin6_211, fin6_212, fin6_213, fin6_214, fin6_215, fin6_216, fin6_217, fin6_218, fin6_219] ++ ([fin6_220, fin6_221, fin6_222, fin6_223, fin6_224, fin6_225, fin6_226, fin6_227, fin6_228, fin6_229, fin6_230, fin6_231, fin6_232, fin6_233, fin6_234, fin6_235, fin6_236, fin6_237, fin6_238, fin6_239] ++ ([fin6_240, fin6_241, fin6_242, fin6_243, fin6_244, fin6_245, fin6_246, fin6_247, fin6_248, fin6_249, fin6_250, fin6_251, fin6_252, fin6_253, fin6_254, fin6_255, fin6_256, fin6_257, fin6_258, fin6_259] ++ ([fin6_260, fin6_261, fin6_262, fin6_263, fin6_264, fin6_265, fin6_266, fin6_267, fin6_268, fin6_269, fin6_270, fin6_271, fin6_272, fin6_273, fin6_274, fin6_275, fin6_276, fin6_277, fin6_278, fin6_279] ++ ([fin6_280, fin6_281, fin6_282, fin6_283, fin6_284, fin6_285, fin6_286, fin6_287, fin6_288, fin6_289, fin6_290, fin6_291, fin6_292, fin6_293, fin6_294, fin6_295, fin6_296, fin6_297, fin6_298, fin6_299] ++ ([fin6_300, fin6_301, fin6_302, fin6_303, fin6_304, fin6_305, fin6_306, fin6_307])))))))))))))))) = true
  rw [allNat_append', seven_leaf_6_0, Bool.true_and, allNat_append', seven_leaf_6_1, Bool.true_and, allNat_append', seven_leaf_6_2, Bool.true_and, allNat_append', seven_leaf_6_3, Bool.true_and, allNat_append', seven_leaf_6_4, Bool.true_and, allNat_append', seven_leaf_6_5, Bool.true_and, allNat_append', seven_leaf_6_6, Bool.true_and, allNat_append', seven_leaf_6_7, Bool.true_and, allNat_append', seven_leaf_6_8, Bool.true_and, allNat_append', seven_leaf_6_9, Bool.true_and, allNat_append', seven_leaf_6_10, Bool.true_and, allNat_append', seven_leaf_6_11, Bool.true_and, allNat_append', seven_leaf_6_12, Bool.true_and, allNat_append', seven_leaf_6_13, Bool.true_and, allNat_append', seven_leaf_6_14, Bool.true_and]
  exact seven_leaf_6_15

theorem seven_fam_6 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 3 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = excRep6.getD 3 0 := seed7_6
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_6 ord7_6_perm (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) finT_6 (by rw [← fam7_6_eq]; exact seven_dfs_6) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_6 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
