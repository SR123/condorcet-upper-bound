/-
CDCert.K6.Seven.S00 — GENERATED (Claude's generator `mksevens.py`): **seven-level seed family 0**
(seed type 0, bottom slice B_6).

* `seven_leaves_0`: the leaf inequality holds at every final state of the family (the chunk checks
  `seven_leaf_0_k` of `CDCert.K6.Seven.L00_*`, 7 chunks, 130 final states);
* `seven_fam_0`: a seven-domain `J` whose bottom six-slice at label 6 has the
  mask of `excRep6[0]` satisfies `2ηD |J| ≤ 2D Λ(J)` (`fam_find` with the DFS check `seven_dfs_0`,
  the leaves, `expand1_maskOf` and `leaf7_sem`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.FamSem
import CDCert.K6.Seven.D00
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.Desc
import CDCert.K6.AllNat
import CDCert.K6.Seven.L00_00

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples CDCert.ListOrder

set_option autoImplicit false
set_option maxRecDepth 100000

theorem seven_leaves_0 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) (encS (expand1 s))) (finT_0).keys = true := by
  rw [finT_0_keys]
  show allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 4320 (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) (encS (expand1 s))) ([fin0_0, fin0_1, fin0_2, fin0_3, fin0_4, fin0_5, fin0_6, fin0_7, fin0_8, fin0_9, fin0_10, fin0_11, fin0_12, fin0_13, fin0_14, fin0_15, fin0_16, fin0_17, fin0_18, fin0_19] ++ ([fin0_20, fin0_21, fin0_22, fin0_23, fin0_24, fin0_25, fin0_26, fin0_27, fin0_28, fin0_29, fin0_30, fin0_31, fin0_32, fin0_33, fin0_34, fin0_35, fin0_36, fin0_37, fin0_38, fin0_39] ++ ([fin0_40, fin0_41, fin0_42, fin0_43, fin0_44, fin0_45, fin0_46, fin0_47, fin0_48, fin0_49, fin0_50, fin0_51, fin0_52, fin0_53, fin0_54, fin0_55, fin0_56, fin0_57, fin0_58, fin0_59] ++ ([fin0_60, fin0_61, fin0_62, fin0_63, fin0_64, fin0_65, fin0_66, fin0_67, fin0_68, fin0_69, fin0_70, fin0_71, fin0_72, fin0_73, fin0_74, fin0_75, fin0_76, fin0_77, fin0_78, fin0_79] ++ ([fin0_80, fin0_81, fin0_82, fin0_83, fin0_84, fin0_85, fin0_86, fin0_87, fin0_88, fin0_89, fin0_90, fin0_91, fin0_92, fin0_93, fin0_94, fin0_95, fin0_96, fin0_97, fin0_98, fin0_99] ++ ([fin0_100, fin0_101, fin0_102, fin0_103, fin0_104, fin0_105, fin0_106, fin0_107, fin0_108, fin0_109, fin0_110, fin0_111, fin0_112, fin0_113, fin0_114, fin0_115, fin0_116, fin0_117, fin0_118, fin0_119] ++ ([fin0_120, fin0_121, fin0_122, fin0_123, fin0_124, fin0_125, fin0_126, fin0_127, fin0_128, fin0_129]))))))) = true
  rw [allNat_append', seven_leaf_0_0, Bool.true_and, allNat_append', seven_leaf_0_1, Bool.true_and, allNat_append', seven_leaf_0_2, Bool.true_and, allNat_append', seven_leaf_0_3, Bool.true_and, allNat_append', seven_leaf_0_4, Bool.true_and, allNat_append', seven_leaf_0_5, Bool.true_and]
  exact seven_leaf_0_6

theorem seven_fam_0 {J : List Nat → Bool} (hJ : IsDom 7 J)
    (hs : maskOf (baseB 5) (botP 6 J) = excRep6.getD 0 0) : 2 * (cE : Int) * card 7 J ≤ lamD J := by
  have hseed : (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) = excRep6.getD 0 0 := seed7_0
  have h6 : (6 : Nat) < 7 := by decide
  have hb := maskOf_copy1_block J h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hb
  have hfind := fam_find copy1 (fun x hx => mem_copy1.mp hx) length_copy1 mkS1 (fun _ => rfl) ocG1 ocG1_sem
    ord7_0 ord7_0_perm (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) finT_0 (by rw [← fam7_0_eq]; exact seven_dfs_0) hJ hb (by decide)
  have hleaf := (allNat_iff' _ _).mp seven_leaves_0 (maskOf copy1 J) (KTree.mem_keys_of_find_ne_zero _ _ hfind)
  rw [expand1_maskOf] at hleaf
  have hk := blk720_bot (J := J) h6
  rw [show 720 * 6 = 4320 from rfl, hs, ← hseed] at hk
  exact leaf7_sem (Or.inl hJ) hk hleaf

end CDCert.K6
