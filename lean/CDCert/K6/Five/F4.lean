/-
CDCert.K6.Five.F4 — GENERATED kernel checks (Claude's generator `mkfivethm.py`) for the
five-level coverage (four-type tower). Every nonempty four-label domain of `groupsEP 4` is mapped by a hinted
relabelling row onto one of the 45 four-type representatives.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs5`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Data5
import CDCert.K6.Defs5

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem five_F4 : dfs1 (leafW rows4 24 45 hint4 rep4T) groups4 (enc (nat_lit 0xffffff)) = true := by
  decide +kernel

end CDCert.K6
