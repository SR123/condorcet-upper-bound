/-
CDCert.K6.Seven.HintIso — GENERATED (Claude's generator `mkdesc.py`) from the kernel-checked
witnesses of `CDCert.K6.Seven.CheckS`: every S hint `hintS.find m = h + 1` names an S type `h < 9`
and a relabelling row over `baseB 5` mapping `m` onto `excRep6.getD h 0`. Case analysis only.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.CheckS

namespace CDCert.K6

open CDCert CDCert.Examples

set_option maxRecDepth 100000

theorem perm6S_0_mem : [0, 1, 2, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6S_1_mem : [0, 1, 2, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_2_mem : [0, 1, 2, 4, 3, 5] ∈ orders 6 := by decide +kernel
theorem perm6S_4_mem : [0, 1, 2, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_6_mem : [0, 1, 3, 2, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6S_7_mem : [0, 1, 3, 2, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_24_mem : [0, 2, 1, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6S_25_mem : [0, 2, 1, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_28_mem : [0, 2, 1, 5, 3, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_33_mem : [0, 2, 3, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6S_35_mem : [0, 2, 3, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6S_57_mem : [0, 3, 2, 4, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6S_59_mem : [0, 3, 2, 5, 4, 1] ∈ orders 6 := by decide +kernel
theorem perm6S_120_mem : [1, 0, 2, 3, 4, 5] ∈ orders 6 := by decide +kernel
theorem perm6S_121_mem : [1, 0, 2, 3, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_127_mem : [1, 0, 3, 2, 5, 4] ∈ orders 6 := by decide +kernel
theorem perm6S_153_mem : [1, 2, 3, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_155_mem : [1, 2, 3, 5, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_159_mem : [1, 2, 4, 3, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_177_mem : [1, 3, 2, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_179_mem : [1, 3, 2, 5, 4, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_255_mem : [2, 0, 4, 3, 5, 1] ∈ orders 6 := by decide +kernel
theorem perm6S_273_mem : [2, 1, 3, 4, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_279_mem : [2, 1, 4, 3, 5, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_287_mem : [2, 1, 5, 4, 3, 0] ∈ orders 6 := by decide +kernel
theorem perm6S_321_mem : [2, 4, 1, 3, 5, 0] ∈ orders 6 := by decide +kernel

/-- **Every S hint is certified.** -/
theorem hint_iso : ∀ m h, hintS.find m = h + 1 → h < 9 ∧ ∃ σ, σ ∈ orders 6 ∧
    relabelI ((baseB 5).map (fun M => idxB (rlab σ M))) m = excRep6.getD h 0 := by
  intro m h hm
  have hk : m ∈ hintS.keys := KTree.mem_keys_of_find_ne_zero hintS m (by rw [hm]; omega)
  rw [hintS_keys] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hv : hintS.find (nat_lit 0x130cf000000000000000000000000000000000000000000000000000000000482000000000000000000000000000000000000000000000000000000000000) = 1 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 1 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 3, 2, 5, 4], perm6S_7_mem, by rw [← rowS_7_eq]; exact hintWit_4⟩
  · have hv : hintS.find (nat_lit 0x3c0c38000000000000000000000000000000000000000000000000000000040012000000000000000000000000000000000000000000000000000000000000) = 1 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 1 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 4, 5, 1], perm6S_33_mem, by rw [← rowS_33_eq]; exact hintWit_6⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 2 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 2 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 5, 4], perm6S_1_mem, by rw [← rowS_1_eq]; exact hintWit_13⟩
  · have hv : hintS.find (nat_lit 0x345000000000000340c001400000005d70000000000005c04005d00000004b2000000000000480000cb8000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_47⟩
  · have hv : hintS.find (nat_lit 0x345000000000000340e001400000005d70000000000005c04005d00000004b2000000000000480000cb0000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [2, 1, 5, 4, 3, 0], perm6S_287_mem, by rw [← rowS_287_eq]; exact hintWit_45⟩
  · have hv : hintS.find (nat_lit 0x5d70000000000005c00005c0000000145000000000000140000140000000145000000000000140000140000000000000000000000000000000000000000000000000000000000000000) = 4 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 4 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_17⟩
  · have hv : hintS.find (nat_lit 0x5d70000000000005c00005d040000014500000000000014000014040000014d000000000000140000340e00000000000000000000000000000000000000000000000000000000000000) = 7 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 7 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 4, 3, 5, 0], perm6S_159_mem, by rw [← rowS_159_eq]; exact hintWit_35⟩
  · have hv : hintS.find (nat_lit 0x5d70000000000005c00005d040000014d000000000000140000340e00000145000000000000140000140400000000000000000000000000000000000000000000000000000000000000) = 7 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 7 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_27⟩
  · have hv : hintS.find (nat_lit 0x5d70000000000005d04005c0000000345000000000000340e00140000000145000000000000140400140000000000000000000000000000000000000000000000000000000000000000) = 7 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 7 := by omega
    subst hj
    exact ⟨by decide, [2, 1, 3, 4, 5, 0], perm6S_273_mem, by rw [← rowS_273_eq]; exact hintWit_52⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 2 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 2 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 4, 5, 1], perm6S_33_mem, by rw [← rowS_33_eq]; exact hintWit_16⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c300030cf0000000000000000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 5, 4, 1], perm6S_35_mem, by rw [← rowS_35_eq]; exact hintWit_20⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c300030cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 3, 2, 5, 4, 1], perm6S_59_mem, by rw [← rowS_59_eq]; exact hintWit_22⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c300034cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 5, 4, 0], perm6S_155_mem, by rw [← rowS_155_eq]; exact hintWit_51⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c300130cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 3, 2, 5, 4, 0], perm6S_179_mem, by rw [← rowS_179_eq]; exact hintWit_54⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c380030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 4, 5, 1], perm6S_33_mem, by rw [← rowS_33_eq]; exact hintWit_23⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0c380130cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 3, 2, 5, 4, 1], perm6S_59_mem, by rw [← rowS_59_eq]; exact hintWit_53⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0e300030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 3, 2, 4, 5, 1], perm6S_57_mem, by rw [← rowS_57_eq]; exact hintWit_21⟩
  · have hv : hintS.find (nat_lit 0x30cf0000000000000000003c0e300034cf0000000000000000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 5, 4, 1], perm6S_35_mem, by rw [← rowS_35_eq]; exact hintWit_50⟩
  · have hv : hintS.find (nat_lit 0x34cf000000000000000000000000000000000000000000000000000000000141000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 1 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 1 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_5⟩
  · have hv : hintS.find (nat_lit 0x34cf0000000000000000003c0c300030cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_28⟩
  · have hv : hintS.find (nat_lit 0x34cf0000000000000000003c0c300130cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 3, 2, 5, 4, 0], perm6S_179_mem, by rw [← rowS_179_eq]; exact hintWit_37⟩
  · have hv : hintS.find (nat_lit 0x34cf0000000000000000003c0c380030cf0000000000000000003c0e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 3, 4, 5, 1], perm6S_33_mem, by rw [← rowS_33_eq]; exact hintWit_26⟩
  · have hv : hintS.find (nat_lit 0x34cf0000000000000000003c0c380130cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 4, 5, 0], perm6S_153_mem, by rw [← rowS_153_eq]; exact hintWit_36⟩
  · have hv : hintS.find (nat_lit 0x130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000141000000000000000000000000000000000000000000000000000000) = 1 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 1 := by omega
    subst hj
    exact ⟨by decide, [1, 3, 2, 4, 5, 0], perm6S_177_mem, by rw [← rowS_177_eq]; exact hintWit_43⟩
  · have hv : hintS.find (nat_lit 0x130cf0000000000000000003c0c300034cf0000000000000000003c0c38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 2, 3, 5, 4, 0], perm6S_155_mem, by rw [← rowS_155_eq]; exact hintWit_44⟩
  · have hv : hintS.find (nat_lit 0x130cf0000000000000000003c0e300034cf0000000000000000003c0c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 3, 2, 4, 5, 0], perm6S_177_mem, by rw [← rowS_177_eq]; exact hintWit_46⟩
  · have hv : hintS.find (nat_lit 0x300cc3000000000000cf0030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 2 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 2 := by omega
    subst hj
    exact ⟨by decide, [2, 0, 4, 3, 5, 1], perm6S_255_mem, by rw [← rowS_255_eq]; exact hintWit_1⟩
  · have hv : hintS.find (nat_lit 0x34cf000000000000000000000000000000000000000000000000000000000141000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 1 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 1 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_2⟩
  · have hv : hintS.find (nat_lit 0x300cc3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000) = 0 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 0 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_0⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 2 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 2 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_7⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf0000000000000000000030cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 5, 4], perm6S_1_mem, by rw [← rowS_1_eq]; exact hintWit_8⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 3, 2, 5, 4], perm6S_7_mem, by rw [← rowS_7_eq]; exact hintWit_10⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf0000000000000000000034cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 0, 2, 3, 5, 4], perm6S_121_mem, by rw [← rowS_121_eq]; exact hintWit_12⟩
  · have hv : hintS.find (nat_lit 0x30cf0030cf0000000000000000000130cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 0, 3, 2, 5, 4], perm6S_127_mem, by rw [← rowS_127_eq]; exact hintWit_11⟩
  · have hv : hintS.find (nat_lit 0x30cf0034cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_24⟩
  · have hv : hintS.find (nat_lit 0x30cf0034cf0000000000000000000130cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 3, 2, 5, 4], perm6S_7_mem, by rw [← rowS_7_eq]; exact hintWit_25⟩
  · have hv : hintS.find (nat_lit 0x30cf0130cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 3, 2, 4, 5], perm6S_6_mem, by rw [← rowS_6_eq]; exact hintWit_33⟩
  · have hv : hintS.find (nat_lit 0x30cf0130cf0000000000000000000034cf0034cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 5, 4], perm6S_1_mem, by rw [← rowS_1_eq]; exact hintWit_34⟩
  · have hv : hintS.find (nat_lit 0x34cf0030cf0000000000000000000030cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 5 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 5 := by omega
    subst hj
    exact ⟨by decide, [1, 0, 2, 3, 4, 5], perm6S_120_mem, by rw [← rowS_120_eq]; exact hintWit_48⟩
  · have hv : hintS.find (nat_lit 0x34cf0030cf0000000000000000000130cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 0, 3, 2, 5, 4], perm6S_127_mem, by rw [← rowS_127_eq]; exact hintWit_49⟩
  · have hv : hintS.find (nat_lit 0x34cf0034cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_29⟩
  · have hv : hintS.find (nat_lit 0x34cf0034cf0000000000000000000130cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 6 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 6 := by omega
    subst hj
    exact ⟨by decide, [1, 0, 2, 3, 4, 5], perm6S_120_mem, by rw [← rowS_120_eq]; exact hintWit_31⟩
  · have hv : hintS.find (nat_lit 0x50000050001450000000000000000170000170005d7000000000000000012000012000492000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 4 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 4 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 5, 4], perm6S_1_mem, by rw [← rowS_1_eq]; exact hintWit_9⟩
  · have hv : hintS.find (nat_lit 0x500300d00014d0000000000000400170010170005d70000000000004c0032000012000c92000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 1, 3, 4, 5], perm6S_24_mem, by rw [← rowS_24_eq]; exact hintWit_3⟩
  · have hv : hintS.find (nat_lit 0x170000170005d7000000000000000005000005000145000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 4 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 4 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_19⟩
  · have hv : hintS.find (nat_lit 0x170410170005d700000000000000000500100500014500000000000000000501300d00014d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 7 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 7 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 4, 3, 5], perm6S_2_mem, by rw [← rowS_2_eq]; exact hintWit_39⟩
  · have hv : hintS.find (nat_lit 0x170410170005d700000000000000000501300d00014d000000000000000005001005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 7 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 7 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_38⟩
  · have hv : hintS.find (nat_lit 0x10170400170005d700000000000000300d00000500034500000000000000000501300d00014d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 5, 4], perm6S_1_mem, by rw [← rowS_1_eq]; exact hintWit_41⟩
  · have hv : hintS.find (nat_lit 0x10170400170005d700000000000001300d00000500034500000000000000000500300d00014d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 1, 5, 3, 4], perm6S_28_mem, by rw [← rowS_28_eq]; exact hintWit_42⟩
  · have hv : hintS.find (nat_lit 0x300d0000050003450000000000000010170400170005d70000000000000000124c00320004b2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_40⟩
  · have hv : hintS.find (nat_lit 0x400170010170005d700000000000000000500300d00014d00000000000001300d000005000345000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 2, 1, 3, 5, 4], perm6S_25_mem, by rw [← rowS_25_eq]; exact hintWit_30⟩
  · have hv : hintS.find (nat_lit 0x400170010170005d700000000000000000501300d00014d00000000000000300d000005000345000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 8 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 8 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 5, 3, 4], perm6S_4_mem, by rw [← rowS_4_eq]; exact hintWit_32⟩
  · have hv : hintS.find (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 3 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 3 := by omega
    subst hj
    exact ⟨by decide, [0, 1, 2, 3, 4, 5], perm6S_0_mem, by rw [← rowS_0_eq]; exact hintWit_18⟩
  · have hv : hintS.find (nat_lit 0x4800000000000000000000000000030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 0 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 0 := by omega
    subst hj
    exact ⟨by decide, [2, 1, 4, 3, 5, 0], perm6S_279_mem, by rw [← rowS_279_eq]; exact hintWit_15⟩
  · have hv : hintS.find (nat_lit 0x120000000000000000000000000000030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) = 0 + 1 := by decide +kernel
    rw [hv] at hm
    have hj : h = 0 := by omega
    subst hj
    exact ⟨by decide, [2, 4, 1, 3, 5, 0], perm6S_321_mem, by rw [← rowS_321_eq]; exact hintWit_14⟩

end CDCert.K6
