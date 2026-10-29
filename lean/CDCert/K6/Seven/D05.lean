/-
CDCert.K6.Seven.D05 — GENERATED kernel check (Claude's generators `mkseven2.py`, `mkfamb.py`) of the
seven-level seed family 5, over the re-ordered family `fam7b_5` (`CDCert.K6.Seven.FamBDef`):
every final state is listed. Evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs7`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Seven.Data
import CDCert.K6.Seven.Fin05
import CDCert.K6.Seven.FamBDef
namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem seven_dfs_5 : dfsP (leafF finT_5) (wp fam7b_5 fullcE (badMask 4320 (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (enc fullc) = true := by
  decide +kernel

end CDCert.K6
