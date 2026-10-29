/-
CDCert.K6.Seven.S01 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 1**
(seed type 0, top slice T_6).

* `seven_leaves_1`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_1_k` of `CDCert.K6.Seven.L01_*`, 7 chunks, 130 final states);
* `seven_fam_1`: a seven-domain `J` whose top six-slice at label 6 has the
  mask of `excRep6[0]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_1`,
  the leaves, `expand3_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D01
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L01_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_1 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) (encS (expand3 s))) (finT_1).keys = true := by
  rw [finT_1_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) (encS (expand3 s))) ([fin1_0, fin1_1, fin1_2, fin1_3, fin1_4, fin1_5, fin1_6, fin1_7, fin1_8, fin1_9, fin1_10, fin1_11, fin1_12, fin1_13, fin1_14, fin1_15, fin1_16, fin1_17, fin1_18, fin1_19] ++ ([fin1_20, fin1_21, fin1_22, fin1_23, fin1_24, fin1_25, fin1_26, fin1_27, fin1_28, fin1_29, fin1_30, fin1_31, fin1_32, fin1_33, fin1_34, fin1_35, fin1_36, fin1_37, fin1_38, fin1_39] ++ ([fin1_40, fin1_41, fin1_42, fin1_43, fin1_44, fin1_45, fin1_46, fin1_47, fin1_48, fin1_49, fin1_50, fin1_51, fin1_52, fin1_53, fin1_54, fin1_55, fin1_56, fin1_57, fin1_58, fin1_59] ++ ([fin1_60, fin1_61, fin1_62, fin1_63, fin1_64, fin1_65, fin1_66, fin1_67, fin1_68, fin1_69, fin1_70, fin1_71, fin1_72, fin1_73, fin1_74, fin1_75, fin1_76, fin1_77, fin1_78, fin1_79] ++ ([fin1_80, fin1_81, fin1_82, fin1_83, fin1_84, fin1_85, fin1_86, fin1_87, fin1_88, fin1_89, fin1_90, fin1_91, fin1_92, fin1_93, fin1_94, fin1_95, fin1_96, fin1_97, fin1_98, fin1_99] ++ ([fin1_100, fin1_101, fin1_102, fin1_103, fin1_104, fin1_105, fin1_106, fin1_107, fin1_108, fin1_109, fin1_110, fin1_111, fin1_112, fin1_113, fin1_114, fin1_115, fin1_116, fin1_117, fin1_118, fin1_119] ++ ([fin1_120, fin1_121, fin1_122, fin1_123, fin1_124, fin1_125, fin1_126, fin1_127, fin1_128, fin1_129]))))))) = true
  rw [allNat_append', seven_leaf_1_0, Bool.true_and, allNat_append', seven_leaf_1_1, Bool.true_and, allNat_append', seven_leaf_1_2, Bool.true_and, allNat_append', seven_leaf_1_3, Bool.true_and, allNat_append', seven_leaf_1_4, Bool.true_and, allNat_append', seven_leaf_1_5, Bool.true_and]
  exact seven_leaf_1_6

theorem seven_fam_1 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (topP 6 J) = excRep6.getD 0 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) = excRep6.getD 0 0 := seed7_1
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy3_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy3 (fun x hx => mem_copy3.mp hx) length_copy3 mkS3 (fun _ => rfl) ocG3 ocG3_sem
    ord7_1 ord7_1_perm (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) finT_1 (by rw [← fam7_1_eq]; exact seven_dfs_1) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_1 (maskOf copy3 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand3_maskOf] at hleaf
  have hk := blk720_top (J := J) h6
  rw [show 10080 + 720 * 6 = 14400 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
