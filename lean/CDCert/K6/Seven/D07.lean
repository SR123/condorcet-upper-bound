/-
CDCert.K6.Seven.D07 — GENERATED kernel checks (Claude's generator `mkseven2.py`) of the
seven-level seed families: family 7: every final state is listed.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs7`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Seven.Data
import CDCert.K6.Seven.Fin07
namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem seven_dfs_7 : dfsP (leafF finT_7) (wp fam7_7 fullcE (badMask 4320 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (enc fullc) = true := by
  decide +kernel

end CDCert.K6
