/-
CDCert.K6.Seven.D25 — GENERATED kernel checks (Claude's generator `mkseven2.py`) of the
seven-level seed families: family 25: every final state is listed.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs7`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Seven.Data
import CDCert.K6.Seven.Fin25
namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem seven_dfs_25 : dfsP (leafF finT_25) (wp fam7_25 fullcE (badMask 4320 (nat_lit 0x170010170005d700000000000000000501300d00014d000000000000000005000005000145000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (enc fullc) = true := by
  decide +kernel

end CDCert.K6
