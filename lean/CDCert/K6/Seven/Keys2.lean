/-
CDCert.K6.Seven.Keys2 — kernel check (Claude): the fourteen exceptional six-types are nonempty
(so the empty slice has no S type).

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Theta

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem exc_card_pos : ∀ j, j < 14 → card 6 (memB6 (excRep6.getD j 0)) ≠ 0 := by
  decide +kernel

end CDCert.K6
