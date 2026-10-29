/-
CDCert.K6.Five.F5All — GENERATED assembly (Claude's generator `mkfivethm.py`) of the 45 five-level
extension checks of `CDCert.K6.Five.F5` (no new kernel computation).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Five.F5

namespace CDCert.K6

/-- All 45 four-type representatives. -/
theorem five_F5_all : ∀ r, r ∈ reps4 → dfs1 (leafW rows5 120 1160 hint5 rep5T) groups5n (enc (liftOf lifts5 r)) = true := by
  intro r hr
  simp only [reps4, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← leafWq_eq]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact five_F5_0
  · exact five_F5_1
  · exact five_F5_2
  · exact five_F5_3
  · exact five_F5_4
  · exact five_F5_5
  · exact five_F5_6
  · exact five_F5_7
  · exact five_F5_8
  · exact five_F5_9
  · exact five_F5_10
  · exact five_F5_11
  · exact five_F5_12
  · exact five_F5_13
  · exact five_F5_14
  · exact five_F5_15
  · exact five_F5_16
  · exact five_F5_17
  · exact five_F5_18
  · exact five_F5_19
  · exact five_F5_20
  · exact five_F5_21
  · exact five_F5_22
  · exact five_F5_23
  · exact five_F5_24
  · exact five_F5_25
  · exact five_F5_26
  · exact five_F5_27
  · exact five_F5_28
  · exact five_F5_29
  · exact five_F5_30
  · exact five_F5_31
  · exact five_F5_32
  · exact five_F5_33
  · exact five_F5_34
  · exact five_F5_35
  · exact five_F5_36
  · exact five_F5_37
  · exact five_F5_38
  · exact five_F5_39
  · exact five_F5_40
  · exact five_F5_41
  · exact five_F5_42
  · exact five_F5_43
  · exact five_F5_44

end CDCert.K6
