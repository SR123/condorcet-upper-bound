/-
CDCert.K6.Seven.Keys — kernel checks on the fourteen exceptional six-types `excRep6`
(Claude): the invariant keys of the nine S types are listed in `sKeyT` and pairwise
distinct; and the facts about `R₈ = excRep6.getD 9 0` used by the receiver argument.

* `key6 H`: the invariant key of a six-domain (the packing `sKey` of the sums of its
  five-slice table fields, read from its `base12` mask);
* `sKeys_mem`, `sKeys_nodup`; `r8_notS`: the key of `R₈` is not an S key;
* `r8_card`, `r8_sD`, `r8_rb`, `r8_rt`: `|R₈| = 8`, `D s(R₈) = 0`, `r_b(R₈) = r_t(R₈) = 0`;
* `r8_first`, `r8_last`: all orders of `R₈` start with `0` and end with `5`;
* `r8_top866`, `r8_bot41`: its top slice at `0` has type 866, its bottom slice at `5` type 41.

Each statement is evaluated by the kernel (`decide +kernel`).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Theta

namespace CDCert.K6

open CDCert CDCert.Bits CDCert.Examples

set_option maxRecDepth 100000
set_option Elab.async false

/-- Offsets of the six bottom five-blocks of a `base12` mask. -/
def oB12 : List Nat := [0, 120, 240, 360, 480, 600]
/-- Offsets of the six top five-blocks of a `base12` mask. -/
def oT12 : List Nat := [720, 840, 960, 1080, 1200, 1320]

/-- The invariant key of a six-domain. -/
noncomputable def key6 (H : List Nat → Bool) : Nat := sKey table5 (maskOf base12 H) oB12 oT12

theorem sKeys_mem : ∀ i, i < 9 → sKeyT.find (key6 (memB6 (excRep6.getD i 0))) ≠ 0 := by
  decide +kernel

theorem sKeys_nodup : ((List.range 9).map (fun i => key6 (memB6 (excRep6.getD i 0)))).Nodup := by
  decide +kernel

theorem r8_notS : sKeyT.find (key6 (memB6 (excRep6.getD 9 0))) = 0 := by
  decide +kernel

theorem r8_card : card 6 (memB6 (excRep6.getD 9 0)) = 8 := by
  decide +kernel

theorem r8_sD : sD (memB6 (excRep6.getD 9 0)) = 0 := by
  decide +kernel

theorem r8_rb : rb (memB6 (excRep6.getD 9 0)) = 0 := by
  decide +kernel

theorem r8_rt : rt (memB6 (excRep6.getD 9 0)) = 0 := by
  decide +kernel

theorem r8_first : ∀ M, M ∈ orders 6 → memB6 (excRep6.getD 9 0) M = true → M.head? = some 0 := by
  decide +kernel

theorem r8_last : ∀ M, M ∈ orders 6 → memB6 (excRep6.getD 9 0) M = true → M.getLast? = some 5 := by
  decide +kernel

theorem r8_top866 : isTy 866 (topP 0 (memB6 (excRep6.getD 9 0))) = 1 := by
  decide +kernel

theorem r8_bot41 : isTy 41 (botP 5 (memB6 (excRep6.getD 9 0))) = 1 := by
  decide +kernel

end CDCert.K6
