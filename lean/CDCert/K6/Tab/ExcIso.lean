/-
CDCert.K6.Tab.ExcIso — GENERATED (Claude's generator `mkexciso.py`) from the kernel-checked
witnesses of `CDCert.K6.Tab.CheckAux`: every key of `exc6` (a bottom-indexed six-mask on which
the six-level inequality fails) is mapped by the relabelling row of a permutation of `0..5`
onto one of the exceptional six-types `excRep6.getD j 0`, `j ∈ excIdx`. Case analysis only.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Tab.CheckAux

namespace CDCert.K6

open CDCert CDCert.Examples

set_option maxRecDepth 100000

/-- The exceptional six-types met by the six-level check: T (9–13) and S types 4, 5, 8. -/
def excIdx : List Nat := [4, 5, 8, 9, 10, 11, 12, 13]

theorem perm6_0_mem : [0, 1, 2, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_1_mem : [0, 1, 2, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_2_mem : [0, 1, 2, 4, 3, 5] ∈ orders 6 := by decide +kernel
theorem perm6_3_mem : [0, 1, 2, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_4_mem : [0, 1, 2, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_5_mem : [0, 1, 2, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_6_mem : [0, 1, 3, 2, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_7_mem : [0, 1, 3, 2, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_9_mem : [0, 1, 3, 4, 5, 2] ∈ orders 6 := by decide +kernel
theorem perm6_11_mem : [0, 1, 3, 5, 4, 2] ∈ orders 6 := by decide +kernel
theorem perm6_13_mem : [0, 1, 4, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_15_mem : [0, 1, 4, 3, 5, 2] ∈ orders 6 := by decide +kernel
theorem perm6_16_mem : [0, 1, 4, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_17_mem : [0, 1, 4, 5, 3, 2] ∈ orders 6 := by decide +kernel
theorem perm6_18_mem : [0, 1, 5, 2, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_19_mem : [0, 1, 5, 2, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_21_mem : [0, 1, 5, 3, 4, 2] ∈ orders 6 := by decide +kernel
theorem perm6_22_mem : [0, 1, 5, 4, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_23_mem : [0, 1, 5, 4, 3, 2] ∈ orders 6 := by decide +kernel
theorem perm6_24_mem : [0, 2, 1, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_25_mem : [0, 2, 1, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_26_mem : [0, 2, 1, 4, 3, 5] ∈ orders 6 := by decide +kernel
theorem perm6_27_mem : [0, 2, 1, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_28_mem : [0, 2, 1, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_29_mem : [0, 2, 1, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_30_mem : [0, 2, 3, 1, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_31_mem : [0, 2, 3, 1, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_32_mem : [0, 2, 3, 4, 1, 5] ∈ orders 6 := by decide +kernel
theorem perm6_33_mem : [0, 2, 3, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_34_mem : [0, 2, 3, 5, 1, 4] ∈ orders 6 := by decide +kernel
theorem perm6_35_mem : [0, 2, 3, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_36_mem : [0, 2, 4, 1, 3, 5] ∈ orders 6 := by decide +kernel
theorem perm6_37_mem : [0, 2, 4, 1, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_39_mem : [0, 2, 4, 3, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_40_mem : [0, 2, 4, 5, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_41_mem : [0, 2, 4, 5, 3, 1] ∈ orders 6 := by decide +kernel
theorem perm6_42_mem : [0, 2, 5, 1, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_43_mem : [0, 2, 5, 1, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_44_mem : [0, 2, 5, 3, 1, 4] ∈ orders 6 := by decide +kernel
theorem perm6_45_mem : [0, 2, 5, 3, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_46_mem : [0, 2, 5, 4, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_47_mem : [0, 2, 5, 4, 3, 1] ∈ orders 6 := by decide +kernel
theorem perm6_51_mem : [0, 3, 1, 4, 5, 2] ∈ orders 6 := by decide +kernel
theorem perm6_57_mem : [0, 3, 2, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_59_mem : [0, 3, 2, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_73_mem : [0, 4, 1, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_76_mem : [0, 4, 1, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_79_mem : [0, 4, 2, 1, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_82_mem : [0, 4, 2, 5, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_90_mem : [0, 4, 5, 1, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_92_mem : [0, 4, 5, 2, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_96_mem : [0, 5, 1, 2, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_97_mem : [0, 5, 1, 2, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_100_mem : [0, 5, 1, 4, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_102_mem : [0, 5, 2, 1, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_103_mem : [0, 5, 2, 1, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_105_mem : [0, 5, 2, 3, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_106_mem : [0, 5, 2, 4, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_107_mem : [0, 5, 2, 4, 3, 1] ∈ orders 6 := by decide +kernel
theorem perm6_114_mem : [0, 5, 4, 1, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_120_mem : [1, 0, 2, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_121_mem : [1, 0, 2, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_123_mem : [1, 0, 2, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_124_mem : [1, 0, 2, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_125_mem : [1, 0, 2, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_127_mem : [1, 0, 3, 2, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_129_mem : [1, 0, 3, 4, 5, 2] ∈ orders 6 := by decide +kernel
theorem perm6_131_mem : [1, 0, 3, 5, 4, 2] ∈ orders 6 := by decide +kernel
theorem perm6_133_mem : [1, 0, 4, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_135_mem : [1, 0, 4, 3, 5, 2] ∈ orders 6 := by decide +kernel
theorem perm6_136_mem : [1, 0, 4, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_137_mem : [1, 0, 4, 5, 3, 2] ∈ orders 6 := by decide +kernel
theorem perm6_138_mem : [1, 0, 5, 2, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_139_mem : [1, 0, 5, 2, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_141_mem : [1, 0, 5, 3, 4, 2] ∈ orders 6 := by decide +kernel
theorem perm6_142_mem : [1, 0, 5, 4, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_144_mem : [1, 2, 0, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_145_mem : [1, 2, 0, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_146_mem : [1, 2, 0, 4, 3, 5] ∈ orders 6 := by decide +kernel
theorem perm6_147_mem : [1, 2, 0, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_148_mem : [1, 2, 0, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_149_mem : [1, 2, 0, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_153_mem : [1, 2, 3, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6_155_mem : [1, 2, 3, 5, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6_159_mem : [1, 2, 4, 3, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6_165_mem : [1, 2, 5, 3, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6_193_mem : [1, 4, 0, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_196_mem : [1, 4, 0, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_217_mem : [1, 5, 0, 2, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_240_mem : [2, 0, 1, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_241_mem : [2, 0, 1, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6_243_mem : [2, 0, 1, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_244_mem : [2, 0, 1, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_245_mem : [2, 0, 1, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_249_mem : [2, 0, 3, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_250_mem : [2, 0, 3, 5, 1, 4] ∈ orders 6 := by decide +kernel
theorem perm6_251_mem : [2, 0, 3, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_256_mem : [2, 0, 4, 5, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_258_mem : [2, 0, 5, 1, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_259_mem : [2, 0, 5, 1, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_261_mem : [2, 0, 5, 3, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_262_mem : [2, 0, 5, 4, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_263_mem : [2, 0, 5, 4, 3, 1] ∈ orders 6 := by decide +kernel
theorem perm6_264_mem : [2, 1, 0, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6_267_mem : [2, 1, 0, 4, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_268_mem : [2, 1, 0, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6_269_mem : [2, 1, 0, 5, 4, 3] ∈ orders 6 := by decide +kernel
theorem perm6_273_mem : [2, 1, 3, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6_275_mem : [2, 1, 3, 5, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6_285_mem : [2, 1, 5, 3, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6_291_mem : [2, 3, 0, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_293_mem : [2, 3, 0, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_297_mem : [2, 3, 1, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6_299_mem : [2, 3, 1, 5, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6_411_mem : [3, 2, 0, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6_413_mem : [3, 2, 0, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6_417_mem : [3, 2, 1, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6_481_mem : [4, 0, 1, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_484_mem : [4, 0, 1, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_490_mem : [4, 0, 2, 5, 1, 3] ∈ orders 6 := by decide +kernel
theorem perm6_498_mem : [4, 0, 5, 1, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_505_mem : [4, 1, 0, 2, 5, 3] ∈ orders 6 := by decide +kernel
theorem perm6_508_mem : [4, 1, 0, 5, 2, 3] ∈ orders 6 := by decide +kernel
theorem perm6_601_mem : [5, 0, 1, 2, 4, 3] ∈ orders 6 := by decide +kernel

/-- **Every failing six-mask is a relabelled exceptional type.** -/
theorem exc6_iso : ∀ m, m ∈ exc6keys → ∃ σ, σ ∈ orders 6 ∧ ∃ j, j ∈ excIdx ∧
    relabelI ((baseB 5).map (fun M => idxB (rlab σ M))) m = excRep6.getD j 0 := by
  intro m hm
  simp only [exc6keys, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨[5, 0, 1, 2, 4, 3], perm6_601_mem, 9, by decide, by rw [← rowB_601_eq]; exact excWit_0⟩
  · exact ⟨[0, 5, 1, 2, 3, 4], perm6_96_mem, 9, by decide, by rw [← rowB_96_eq]; exact excWit_1⟩
  · exact ⟨[0, 5, 2, 1, 3, 4], perm6_102_mem, 9, by decide, by rw [← rowB_102_eq]; exact excWit_2⟩
  · exact ⟨[0, 5, 1, 2, 4, 3], perm6_97_mem, 9, by decide, by rw [← rowB_97_eq]; exact excWit_3⟩
  · exact ⟨[0, 5, 1, 4, 2, 3], perm6_100_mem, 9, by decide, by rw [← rowB_100_eq]; exact excWit_4⟩
  · exact ⟨[0, 5, 2, 1, 4, 3], perm6_103_mem, 9, by decide, by rw [← rowB_103_eq]; exact excWit_5⟩
  · exact ⟨[0, 5, 4, 1, 2, 3], perm6_114_mem, 9, by decide, by rw [← rowB_114_eq]; exact excWit_6⟩
  · exact ⟨[0, 5, 2, 3, 4, 1], perm6_105_mem, 9, by decide, by rw [← rowB_105_eq]; exact excWit_7⟩
  · exact ⟨[0, 5, 2, 4, 1, 3], perm6_106_mem, 9, by decide, by rw [← rowB_106_eq]; exact excWit_8⟩
  · exact ⟨[0, 5, 2, 4, 3, 1], perm6_107_mem, 9, by decide, by rw [← rowB_107_eq]; exact excWit_9⟩
  · exact ⟨[1, 5, 0, 2, 4, 3], perm6_217_mem, 9, by decide, by rw [← rowB_217_eq]; exact excWit_10⟩
  · exact ⟨[0, 1, 5, 2, 3, 4], perm6_18_mem, 9, by decide, by rw [← rowB_18_eq]; exact excWit_11⟩
  · exact ⟨[0, 2, 5, 1, 3, 4], perm6_42_mem, 9, by decide, by rw [← rowB_42_eq]; exact excWit_12⟩
  · exact ⟨[0, 2, 5, 3, 1, 4], perm6_44_mem, 9, by decide, by rw [← rowB_44_eq]; exact excWit_13⟩
  · exact ⟨[0, 1, 5, 2, 4, 3], perm6_19_mem, 9, by decide, by rw [← rowB_19_eq]; exact excWit_14⟩
  · exact ⟨[0, 1, 5, 4, 2, 3], perm6_22_mem, 9, by decide, by rw [← rowB_22_eq]; exact excWit_15⟩
  · exact ⟨[0, 2, 5, 1, 4, 3], perm6_43_mem, 9, by decide, by rw [← rowB_43_eq]; exact excWit_16⟩
  · exact ⟨[0, 4, 5, 1, 2, 3], perm6_90_mem, 9, by decide, by rw [← rowB_90_eq]; exact excWit_17⟩
  · exact ⟨[0, 2, 5, 3, 4, 1], perm6_45_mem, 9, by decide, by rw [← rowB_45_eq]; exact excWit_18⟩
  · exact ⟨[0, 2, 5, 4, 1, 3], perm6_46_mem, 9, by decide, by rw [← rowB_46_eq]; exact excWit_19⟩
  · exact ⟨[0, 4, 5, 2, 1, 3], perm6_92_mem, 9, by decide, by rw [← rowB_92_eq]; exact excWit_20⟩
  · exact ⟨[0, 2, 5, 4, 3, 1], perm6_47_mem, 9, by decide, by rw [← rowB_47_eq]; exact excWit_21⟩
  · exact ⟨[1, 0, 5, 2, 3, 4], perm6_138_mem, 9, by decide, by rw [← rowB_138_eq]; exact excWit_22⟩
  · exact ⟨[2, 0, 5, 1, 3, 4], perm6_258_mem, 9, by decide, by rw [← rowB_258_eq]; exact excWit_23⟩
  · exact ⟨[1, 0, 5, 2, 4, 3], perm6_139_mem, 9, by decide, by rw [← rowB_139_eq]; exact excWit_24⟩
  · exact ⟨[1, 0, 5, 4, 2, 3], perm6_142_mem, 9, by decide, by rw [← rowB_142_eq]; exact excWit_25⟩
  · exact ⟨[2, 0, 5, 1, 4, 3], perm6_259_mem, 9, by decide, by rw [← rowB_259_eq]; exact excWit_26⟩
  · exact ⟨[4, 0, 5, 1, 2, 3], perm6_498_mem, 9, by decide, by rw [← rowB_498_eq]; exact excWit_27⟩
  · exact ⟨[2, 0, 5, 3, 4, 1], perm6_261_mem, 9, by decide, by rw [← rowB_261_eq]; exact excWit_28⟩
  · exact ⟨[2, 0, 5, 4, 1, 3], perm6_262_mem, 9, by decide, by rw [← rowB_262_eq]; exact excWit_29⟩
  · exact ⟨[2, 0, 5, 4, 3, 1], perm6_263_mem, 9, by decide, by rw [← rowB_263_eq]; exact excWit_30⟩
  · exact ⟨[1, 2, 5, 3, 4, 0], perm6_165_mem, 9, by decide, by rw [← rowB_165_eq]; exact excWit_31⟩
  · exact ⟨[0, 1, 2, 5, 3, 4], perm6_4_mem, 9, by decide, by rw [← rowB_4_eq]; exact excWit_32⟩
  · exact ⟨[0, 2, 1, 5, 3, 4], perm6_28_mem, 9, by decide, by rw [← rowB_28_eq]; exact excWit_33⟩
  · exact ⟨[0, 2, 3, 5, 1, 4], perm6_34_mem, 9, by decide, by rw [← rowB_34_eq]; exact excWit_34⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 9, by decide, by rw [← rowB_5_eq]; exact excWit_35⟩
  · exact ⟨[0, 1, 4, 5, 2, 3], perm6_16_mem, 9, by decide, by rw [← rowB_16_eq]; exact excWit_36⟩
  · exact ⟨[0, 2, 1, 5, 4, 3], perm6_29_mem, 9, by decide, by rw [← rowB_29_eq]; exact excWit_37⟩
  · exact ⟨[0, 4, 1, 5, 2, 3], perm6_76_mem, 9, by decide, by rw [← rowB_76_eq]; exact excWit_38⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 9, by decide, by rw [← rowB_35_eq]; exact excWit_39⟩
  · exact ⟨[0, 2, 4, 5, 1, 3], perm6_40_mem, 9, by decide, by rw [← rowB_40_eq]; exact excWit_40⟩
  · exact ⟨[0, 4, 2, 5, 1, 3], perm6_82_mem, 9, by decide, by rw [← rowB_82_eq]; exact excWit_41⟩
  · exact ⟨[0, 2, 4, 5, 3, 1], perm6_41_mem, 9, by decide, by rw [← rowB_41_eq]; exact excWit_42⟩
  · exact ⟨[1, 0, 2, 5, 3, 4], perm6_124_mem, 9, by decide, by rw [← rowB_124_eq]; exact excWit_43⟩
  · exact ⟨[2, 0, 1, 5, 3, 4], perm6_244_mem, 9, by decide, by rw [← rowB_244_eq]; exact excWit_44⟩
  · exact ⟨[2, 0, 3, 5, 1, 4], perm6_250_mem, 9, by decide, by rw [← rowB_250_eq]; exact excWit_45⟩
  · exact ⟨[1, 0, 2, 5, 4, 3], perm6_125_mem, 9, by decide, by rw [← rowB_125_eq]; exact excWit_46⟩
  · exact ⟨[1, 0, 4, 5, 2, 3], perm6_136_mem, 9, by decide, by rw [← rowB_136_eq]; exact excWit_47⟩
  · exact ⟨[0, 1, 5, 4, 3, 2], perm6_23_mem, 5, by decide, by rw [← rowB_23_eq]; exact excWit_48⟩
  · exact ⟨[0, 1, 4, 5, 3, 2], perm6_17_mem, 5, by decide, by rw [← rowB_17_eq]; exact excWit_49⟩
  · exact ⟨[1, 0, 4, 5, 3, 2], perm6_137_mem, 5, by decide, by rw [← rowB_137_eq]; exact excWit_50⟩
  · exact ⟨[0, 1, 4, 5, 3, 2], perm6_17_mem, 11, by decide, by rw [← rowB_17_eq]; exact excWit_51⟩
  · exact ⟨[2, 0, 1, 5, 4, 3], perm6_245_mem, 9, by decide, by rw [← rowB_245_eq]; exact excWit_52⟩
  · exact ⟨[4, 0, 1, 5, 2, 3], perm6_484_mem, 9, by decide, by rw [← rowB_484_eq]; exact excWit_53⟩
  · exact ⟨[2, 0, 3, 5, 4, 1], perm6_251_mem, 9, by decide, by rw [← rowB_251_eq]; exact excWit_54⟩
  · exact ⟨[0, 1, 3, 5, 4, 2], perm6_11_mem, 10, by decide, by rw [← rowB_11_eq]; exact excWit_55⟩
  · exact ⟨[2, 0, 4, 5, 1, 3], perm6_256_mem, 9, by decide, by rw [← rowB_256_eq]; exact excWit_56⟩
  · exact ⟨[4, 0, 2, 5, 1, 3], perm6_490_mem, 9, by decide, by rw [← rowB_490_eq]; exact excWit_57⟩
  · exact ⟨[1, 2, 0, 5, 4, 3], perm6_149_mem, 9, by decide, by rw [← rowB_149_eq]; exact excWit_58⟩
  · exact ⟨[1, 4, 0, 5, 2, 3], perm6_196_mem, 9, by decide, by rw [← rowB_196_eq]; exact excWit_59⟩
  · exact ⟨[2, 1, 0, 5, 4, 3], perm6_269_mem, 9, by decide, by rw [← rowB_269_eq]; exact excWit_60⟩
  · exact ⟨[4, 1, 0, 5, 2, 3], perm6_508_mem, 9, by decide, by rw [← rowB_508_eq]; exact excWit_61⟩
  · exact ⟨[2, 3, 0, 5, 4, 1], perm6_293_mem, 9, by decide, by rw [← rowB_293_eq]; exact excWit_62⟩
  · exact ⟨[1, 2, 3, 5, 4, 0], perm6_155_mem, 9, by decide, by rw [← rowB_155_eq]; exact excWit_63⟩
  · exact ⟨[2, 1, 3, 5, 4, 0], perm6_275_mem, 9, by decide, by rw [← rowB_275_eq]; exact excWit_64⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 10, by decide, by rw [← rowB_35_eq]; exact excWit_65⟩
  · exact ⟨[2, 3, 1, 5, 4, 0], perm6_299_mem, 9, by decide, by rw [← rowB_299_eq]; exact excWit_66⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 9, by decide, by rw [← rowB_1_eq]; exact excWit_67⟩
  · exact ⟨[0, 2, 1, 3, 5, 4], perm6_25_mem, 9, by decide, by rw [← rowB_25_eq]; exact excWit_68⟩
  · exact ⟨[0, 2, 3, 1, 5, 4], perm6_31_mem, 9, by decide, by rw [← rowB_31_eq]; exact excWit_69⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 9, by decide, by rw [← rowB_3_eq]; exact excWit_70⟩
  · exact ⟨[0, 1, 4, 2, 5, 3], perm6_13_mem, 9, by decide, by rw [← rowB_13_eq]; exact excWit_71⟩
  · exact ⟨[0, 2, 1, 4, 5, 3], perm6_27_mem, 9, by decide, by rw [← rowB_27_eq]; exact excWit_72⟩
  · exact ⟨[0, 4, 1, 2, 5, 3], perm6_73_mem, 9, by decide, by rw [← rowB_73_eq]; exact excWit_73⟩
  · exact ⟨[0, 2, 3, 4, 5, 1], perm6_33_mem, 9, by decide, by rw [← rowB_33_eq]; exact excWit_74⟩
  · exact ⟨[0, 2, 4, 1, 5, 3], perm6_37_mem, 9, by decide, by rw [← rowB_37_eq]; exact excWit_75⟩
  · exact ⟨[0, 4, 2, 1, 5, 3], perm6_79_mem, 9, by decide, by rw [← rowB_79_eq]; exact excWit_76⟩
  · exact ⟨[0, 2, 4, 3, 5, 1], perm6_39_mem, 9, by decide, by rw [← rowB_39_eq]; exact excWit_77⟩
  · exact ⟨[0, 1, 5, 2, 3, 4], perm6_18_mem, 10, by decide, by rw [← rowB_18_eq]; exact excWit_78⟩
  · exact ⟨[1, 0, 2, 3, 5, 4], perm6_121_mem, 9, by decide, by rw [← rowB_121_eq]; exact excWit_79⟩
  · exact ⟨[2, 0, 1, 3, 5, 4], perm6_241_mem, 9, by decide, by rw [← rowB_241_eq]; exact excWit_80⟩
  · exact ⟨[0, 1, 5, 4, 3, 2], perm6_23_mem, 10, by decide, by rw [← rowB_23_eq]; exact excWit_81⟩
  · exact ⟨[1, 0, 2, 4, 5, 3], perm6_123_mem, 9, by decide, by rw [← rowB_123_eq]; exact excWit_82⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 5, by decide, by rw [← rowB_5_eq]; exact excWit_83⟩
  · exact ⟨[0, 1, 3, 5, 4, 2], perm6_11_mem, 5, by decide, by rw [← rowB_11_eq]; exact excWit_84⟩
  · exact ⟨[1, 0, 2, 5, 4, 3], perm6_125_mem, 5, by decide, by rw [← rowB_125_eq]; exact excWit_85⟩
  · exact ⟨[1, 0, 3, 5, 4, 2], perm6_131_mem, 5, by decide, by rw [← rowB_131_eq]; exact excWit_86⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 5, by decide, by rw [← rowB_3_eq]; exact excWit_87⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 11, by decide, by rw [← rowB_5_eq]; exact excWit_88⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 5, by decide, by rw [← rowB_9_eq]; exact excWit_89⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 12, by decide, by rw [← rowB_5_eq]; exact excWit_90⟩
  · exact ⟨[0, 1, 3, 5, 4, 2], perm6_11_mem, 11, by decide, by rw [← rowB_11_eq]; exact excWit_91⟩
  · exact ⟨[1, 0, 2, 4, 5, 3], perm6_123_mem, 5, by decide, by rw [← rowB_123_eq]; exact excWit_92⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 11, by decide, by rw [← rowB_3_eq]; exact excWit_93⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 12, by decide, by rw [← rowB_3_eq]; exact excWit_94⟩
  · exact ⟨[1, 0, 4, 2, 5, 3], perm6_133_mem, 9, by decide, by rw [← rowB_133_eq]; exact excWit_95⟩
  · exact ⟨[0, 1, 5, 2, 4, 3], perm6_19_mem, 5, by decide, by rw [← rowB_19_eq]; exact excWit_96⟩
  · exact ⟨[0, 1, 5, 3, 4, 2], perm6_21_mem, 5, by decide, by rw [← rowB_21_eq]; exact excWit_97⟩
  · exact ⟨[1, 0, 5, 2, 4, 3], perm6_139_mem, 5, by decide, by rw [← rowB_139_eq]; exact excWit_98⟩
  · exact ⟨[1, 0, 5, 3, 4, 2], perm6_141_mem, 5, by decide, by rw [← rowB_141_eq]; exact excWit_99⟩
  · exact ⟨[0, 1, 4, 3, 5, 2], perm6_15_mem, 5, by decide, by rw [← rowB_15_eq]; exact excWit_100⟩
  · exact ⟨[0, 1, 5, 2, 4, 3], perm6_19_mem, 12, by decide, by rw [← rowB_19_eq]; exact excWit_101⟩
  · exact ⟨[0, 1, 5, 3, 4, 2], perm6_21_mem, 11, by decide, by rw [← rowB_21_eq]; exact excWit_102⟩
  · exact ⟨[2, 0, 1, 4, 5, 3], perm6_243_mem, 9, by decide, by rw [← rowB_243_eq]; exact excWit_103⟩
  · exact ⟨[4, 0, 1, 2, 5, 3], perm6_481_mem, 9, by decide, by rw [← rowB_481_eq]; exact excWit_104⟩
  · exact ⟨[2, 0, 3, 4, 5, 1], perm6_249_mem, 9, by decide, by rw [← rowB_249_eq]; exact excWit_105⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 10, by decide, by rw [← rowB_9_eq]; exact excWit_106⟩
  · exact ⟨[1, 0, 3, 4, 5, 2], perm6_129_mem, 5, by decide, by rw [← rowB_129_eq]; exact excWit_107⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 12, by decide, by rw [← rowB_9_eq]; exact excWit_108⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 11, by decide, by rw [← rowB_9_eq]; exact excWit_109⟩
  · exact ⟨[1, 2, 0, 4, 5, 3], perm6_147_mem, 9, by decide, by rw [← rowB_147_eq]; exact excWit_110⟩
  · exact ⟨[1, 4, 0, 2, 5, 3], perm6_193_mem, 9, by decide, by rw [← rowB_193_eq]; exact excWit_111⟩
  · exact ⟨[2, 1, 0, 4, 5, 3], perm6_267_mem, 9, by decide, by rw [← rowB_267_eq]; exact excWit_112⟩
  · exact ⟨[4, 1, 0, 2, 5, 3], perm6_505_mem, 9, by decide, by rw [← rowB_505_eq]; exact excWit_113⟩
  · exact ⟨[2, 3, 0, 4, 5, 1], perm6_291_mem, 9, by decide, by rw [← rowB_291_eq]; exact excWit_114⟩
  · exact ⟨[0, 1, 3, 5, 4, 2], perm6_11_mem, 4, by decide, by rw [← rowB_11_eq]; exact excWit_115⟩
  · exact ⟨[0, 1, 4, 5, 3, 2], perm6_17_mem, 13, by decide, by rw [← rowB_17_eq]; exact excWit_116⟩
  · exact ⟨[0, 1, 3, 5, 4, 2], perm6_11_mem, 13, by decide, by rw [← rowB_11_eq]; exact excWit_117⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 4, by decide, by rw [← rowB_9_eq]; exact excWit_118⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 13, by decide, by rw [← rowB_9_eq]; exact excWit_119⟩
  · exact ⟨[0, 1, 4, 3, 5, 2], perm6_15_mem, 13, by decide, by rw [← rowB_15_eq]; exact excWit_120⟩
  · exact ⟨[0, 3, 1, 4, 5, 2], perm6_51_mem, 4, by decide, by rw [← rowB_51_eq]; exact excWit_121⟩
  · exact ⟨[0, 3, 2, 4, 5, 1], perm6_57_mem, 13, by decide, by rw [← rowB_57_eq]; exact excWit_122⟩
  · exact ⟨[1, 0, 3, 4, 5, 2], perm6_129_mem, 4, by decide, by rw [← rowB_129_eq]; exact excWit_123⟩
  · exact ⟨[1, 0, 3, 4, 5, 2], perm6_129_mem, 13, by decide, by rw [← rowB_129_eq]; exact excWit_124⟩
  · exact ⟨[1, 0, 4, 3, 5, 2], perm6_135_mem, 13, by decide, by rw [← rowB_135_eq]; exact excWit_125⟩
  · exact ⟨[1, 2, 3, 4, 5, 0], perm6_153_mem, 4, by decide, by rw [← rowB_153_eq]; exact excWit_126⟩
  · exact ⟨[1, 2, 3, 4, 5, 0], perm6_153_mem, 13, by decide, by rw [← rowB_153_eq]; exact excWit_127⟩
  · exact ⟨[1, 2, 4, 3, 5, 0], perm6_159_mem, 13, by decide, by rw [← rowB_159_eq]; exact excWit_128⟩
  · exact ⟨[2, 1, 3, 4, 5, 0], perm6_273_mem, 13, by decide, by rw [← rowB_273_eq]; exact excWit_129⟩
  · exact ⟨[1, 2, 3, 5, 4, 0], perm6_155_mem, 8, by decide, by rw [← rowB_155_eq]; exact excWit_130⟩
  · exact ⟨[2, 1, 5, 3, 4, 0], perm6_285_mem, 8, by decide, by rw [← rowB_285_eq]; exact excWit_131⟩
  · exact ⟨[0, 2, 3, 4, 5, 1], perm6_33_mem, 13, by decide, by rw [← rowB_33_eq]; exact excWit_132⟩
  · exact ⟨[0, 1, 3, 4, 5, 2], perm6_9_mem, 8, by decide, by rw [← rowB_9_eq]; exact excWit_133⟩
  · exact ⟨[1, 2, 3, 4, 5, 0], perm6_153_mem, 9, by decide, by rw [← rowB_153_eq]; exact excWit_134⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 5, by decide, by rw [← rowB_35_eq]; exact excWit_135⟩
  · exact ⟨[0, 3, 2, 5, 4, 1], perm6_59_mem, 5, by decide, by rw [← rowB_59_eq]; exact excWit_136⟩
  · exact ⟨[1, 2, 3, 5, 4, 0], perm6_155_mem, 5, by decide, by rw [← rowB_155_eq]; exact excWit_137⟩
  · exact ⟨[0, 2, 3, 4, 5, 1], perm6_33_mem, 5, by decide, by rw [← rowB_33_eq]; exact excWit_138⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 11, by decide, by rw [← rowB_35_eq]; exact excWit_139⟩
  · exact ⟨[0, 3, 2, 4, 5, 1], perm6_57_mem, 5, by decide, by rw [← rowB_57_eq]; exact excWit_140⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 12, by decide, by rw [← rowB_35_eq]; exact excWit_141⟩
  · exact ⟨[1, 2, 3, 4, 5, 0], perm6_153_mem, 5, by decide, by rw [← rowB_153_eq]; exact excWit_142⟩
  · exact ⟨[0, 2, 3, 4, 5, 1], perm6_33_mem, 11, by decide, by rw [← rowB_33_eq]; exact excWit_143⟩
  · exact ⟨[0, 2, 3, 4, 5, 1], perm6_33_mem, 12, by decide, by rw [← rowB_33_eq]; exact excWit_144⟩
  · exact ⟨[2, 0, 3, 4, 5, 1], perm6_249_mem, 10, by decide, by rw [← rowB_249_eq]; exact excWit_145⟩
  · exact ⟨[2, 3, 1, 4, 5, 0], perm6_297_mem, 9, by decide, by rw [← rowB_297_eq]; exact excWit_146⟩
  · exact ⟨[2, 3, 0, 5, 4, 1], perm6_293_mem, 5, by decide, by rw [← rowB_293_eq]; exact excWit_147⟩
  · exact ⟨[3, 2, 0, 5, 4, 1], perm6_413_mem, 5, by decide, by rw [← rowB_413_eq]; exact excWit_148⟩
  · exact ⟨[2, 3, 1, 5, 4, 0], perm6_299_mem, 5, by decide, by rw [← rowB_299_eq]; exact excWit_149⟩
  · exact ⟨[2, 3, 0, 4, 5, 1], perm6_291_mem, 5, by decide, by rw [← rowB_291_eq]; exact excWit_150⟩
  · exact ⟨[2, 3, 0, 5, 4, 1], perm6_293_mem, 11, by decide, by rw [← rowB_293_eq]; exact excWit_151⟩
  · exact ⟨[3, 2, 0, 4, 5, 1], perm6_411_mem, 5, by decide, by rw [← rowB_411_eq]; exact excWit_152⟩
  · exact ⟨[2, 3, 0, 5, 4, 1], perm6_293_mem, 12, by decide, by rw [← rowB_293_eq]; exact excWit_153⟩
  · exact ⟨[3, 2, 1, 4, 5, 0], perm6_417_mem, 5, by decide, by rw [← rowB_417_eq]; exact excWit_154⟩
  · exact ⟨[2, 3, 1, 5, 4, 0], perm6_299_mem, 12, by decide, by rw [← rowB_299_eq]; exact excWit_155⟩
  · exact ⟨[3, 2, 0, 4, 5, 1], perm6_411_mem, 11, by decide, by rw [← rowB_411_eq]; exact excWit_156⟩
  · exact ⟨[0, 2, 3, 5, 4, 1], perm6_35_mem, 13, by decide, by rw [← rowB_35_eq]; exact excWit_157⟩
  · exact ⟨[0, 2, 5, 4, 3, 1], perm6_47_mem, 8, by decide, by rw [← rowB_47_eq]; exact excWit_158⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 9, by decide, by rw [← rowB_0_eq]; exact excWit_159⟩
  · exact ⟨[0, 2, 1, 3, 4, 5], perm6_24_mem, 9, by decide, by rw [← rowB_24_eq]; exact excWit_160⟩
  · exact ⟨[0, 2, 3, 1, 4, 5], perm6_30_mem, 9, by decide, by rw [← rowB_30_eq]; exact excWit_161⟩
  · exact ⟨[0, 1, 2, 4, 3, 5], perm6_2_mem, 9, by decide, by rw [← rowB_2_eq]; exact excWit_162⟩
  · exact ⟨[0, 2, 1, 4, 3, 5], perm6_26_mem, 9, by decide, by rw [← rowB_26_eq]; exact excWit_163⟩
  · exact ⟨[0, 2, 3, 4, 1, 5], perm6_32_mem, 9, by decide, by rw [← rowB_32_eq]; exact excWit_164⟩
  · exact ⟨[0, 2, 4, 1, 3, 5], perm6_36_mem, 9, by decide, by rw [← rowB_36_eq]; exact excWit_165⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 10, by decide, by rw [← rowB_3_eq]; exact excWit_166⟩
  · exact ⟨[1, 0, 2, 3, 4, 5], perm6_120_mem, 9, by decide, by rw [← rowB_120_eq]; exact excWit_167⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 5, by decide, by rw [← rowB_1_eq]; exact excWit_168⟩
  · exact ⟨[0, 1, 3, 2, 5, 4], perm6_7_mem, 5, by decide, by rw [← rowB_7_eq]; exact excWit_169⟩
  · exact ⟨[1, 0, 2, 3, 5, 4], perm6_121_mem, 5, by decide, by rw [← rowB_121_eq]; exact excWit_170⟩
  · exact ⟨[1, 0, 3, 2, 5, 4], perm6_127_mem, 5, by decide, by rw [← rowB_127_eq]; exact excWit_171⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 5, by decide, by rw [← rowB_0_eq]; exact excWit_172⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 11, by decide, by rw [← rowB_1_eq]; exact excWit_173⟩
  · exact ⟨[0, 1, 3, 2, 5, 4], perm6_7_mem, 12, by decide, by rw [← rowB_7_eq]; exact excWit_174⟩
  · exact ⟨[0, 1, 3, 2, 4, 5], perm6_6_mem, 5, by decide, by rw [← rowB_6_eq]; exact excWit_175⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 12, by decide, by rw [← rowB_1_eq]; exact excWit_176⟩
  · exact ⟨[0, 1, 3, 2, 5, 4], perm6_7_mem, 11, by decide, by rw [← rowB_7_eq]; exact excWit_177⟩
  · exact ⟨[1, 0, 2, 3, 4, 5], perm6_120_mem, 5, by decide, by rw [← rowB_120_eq]; exact excWit_178⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 11, by decide, by rw [← rowB_0_eq]; exact excWit_179⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 12, by decide, by rw [← rowB_0_eq]; exact excWit_180⟩
  · exact ⟨[2, 0, 1, 3, 4, 5], perm6_240_mem, 9, by decide, by rw [← rowB_240_eq]; exact excWit_181⟩
  · exact ⟨[0, 1, 5, 4, 2, 3], perm6_22_mem, 10, by decide, by rw [← rowB_22_eq]; exact excWit_182⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 4, by decide, by rw [← rowB_1_eq]; exact excWit_183⟩
  · exact ⟨[0, 1, 2, 4, 5, 3], perm6_3_mem, 13, by decide, by rw [← rowB_3_eq]; exact excWit_184⟩
  · exact ⟨[0, 1, 2, 3, 5, 4], perm6_1_mem, 13, by decide, by rw [← rowB_1_eq]; exact excWit_185⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 8, by decide, by rw [← rowB_5_eq]; exact excWit_186⟩
  · exact ⟨[0, 1, 2, 5, 3, 4], perm6_4_mem, 4, by decide, by rw [← rowB_4_eq]; exact excWit_187⟩
  · exact ⟨[0, 1, 2, 5, 4, 3], perm6_5_mem, 13, by decide, by rw [← rowB_5_eq]; exact excWit_188⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 4, by decide, by rw [← rowB_0_eq]; exact excWit_189⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], perm6_0_mem, 13, by decide, by rw [← rowB_0_eq]; exact excWit_190⟩
  · exact ⟨[0, 1, 2, 4, 3, 5], perm6_2_mem, 13, by decide, by rw [← rowB_2_eq]; exact excWit_191⟩
  · exact ⟨[1, 2, 0, 3, 5, 4], perm6_145_mem, 4, by decide, by rw [← rowB_145_eq]; exact excWit_192⟩
  · exact ⟨[1, 2, 0, 4, 5, 3], perm6_147_mem, 13, by decide, by rw [← rowB_147_eq]; exact excWit_193⟩
  · exact ⟨[1, 2, 0, 3, 4, 5], perm6_144_mem, 8, by decide, by rw [← rowB_144_eq]; exact excWit_194⟩
  · exact ⟨[1, 0, 2, 5, 3, 4], perm6_124_mem, 4, by decide, by rw [← rowB_124_eq]; exact excWit_195⟩
  · exact ⟨[1, 0, 2, 5, 4, 3], perm6_125_mem, 13, by decide, by rw [← rowB_125_eq]; exact excWit_196⟩
  · exact ⟨[1, 2, 0, 5, 3, 4], perm6_148_mem, 4, by decide, by rw [← rowB_148_eq]; exact excWit_197⟩
  · exact ⟨[2, 1, 0, 5, 4, 3], perm6_269_mem, 13, by decide, by rw [← rowB_269_eq]; exact excWit_198⟩
  · exact ⟨[1, 2, 0, 3, 4, 5], perm6_144_mem, 4, by decide, by rw [← rowB_144_eq]; exact excWit_199⟩
  · exact ⟨[1, 2, 0, 4, 3, 5], perm6_146_mem, 13, by decide, by rw [← rowB_146_eq]; exact excWit_200⟩
  · exact ⟨[2, 1, 0, 3, 4, 5], perm6_264_mem, 13, by decide, by rw [← rowB_264_eq]; exact excWit_201⟩
  · exact ⟨[1, 2, 0, 3, 5, 4], perm6_145_mem, 8, by decide, by rw [← rowB_145_eq]; exact excWit_202⟩
  · exact ⟨[2, 1, 0, 5, 3, 4], perm6_268_mem, 8, by decide, by rw [← rowB_268_eq]; exact excWit_203⟩

end CDCert.K6
