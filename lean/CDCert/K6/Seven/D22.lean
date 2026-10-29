/-
CDCert.K6.Seven.D22 — GENERATED kernel checks (Claude's generator `mkseven2.py`) of the
seven-level seed families: family 22: every final state is listed.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs7`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Seven.Data
import CDCert.K6.Seven.Fin22
namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem seven_dfs_22 : dfsP (leafF finT_22) (wp fam7_22 fullcE (badMask 4320 (nat_lit 0x34cf0030cf0000000000000000000030cf0130cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (enc fullc) = true := by
  decide +kernel

end CDCert.K6
