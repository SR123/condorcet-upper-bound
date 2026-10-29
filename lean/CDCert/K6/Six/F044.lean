/-
CDCert.K6.Six.F044 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 664, 710, 724, 880, 1017, 1064, 1114, 1142.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs`
and `CDCert.K6.Sound` for the definitions and their soundness.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Data6
import CDCert.K6.Defs

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem six_rep_664 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5cf0034cf))) = true := by
  decide +kernel

theorem six_rep_710 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d70401d7))) = true := by
  decide +kernel

theorem six_rep_724 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34cf0130cf))) = true := by
  decide +kernel

theorem six_rep_880 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x508302d08016d))) = true := by
  decide +kernel

theorem six_rep_1017 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf01300f0003cf))) = true := by
  decide +kernel

theorem six_rep_1064 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d00c340200b40))) = true := by
  decide +kernel

theorem six_rep_1114 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000020c003a0c20ba))) = true := by
  decide +kernel

theorem six_rep_1142 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x304001300000f0034cf))) = true := by
  decide +kernel

end CDCert.K6
