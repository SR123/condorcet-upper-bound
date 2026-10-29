/-
CDCert.K6.Six.F046 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 667, 671, 712, 723, 906, 1030, 1066, 1153.
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

theorem six_rep_667 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5d70005d7))) = true := by
  decide +kernel

theorem six_rep_671 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5d70410d7))) = true := by
  decide +kernel

theorem six_rep_712 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d70410d7))) = true := by
  decide +kernel

theorem six_rep_723 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34cf0034cf))) = true := by
  decide +kernel

theorem six_rep_906 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70410170401d7))) = true := by
  decide +kernel

theorem six_rep_1030 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x170410170005d7))) = true := by
  decide +kernel

theorem six_rep_1066 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f300c3c0300cc0))) = true := by
  decide +kernel

theorem six_rep_1153 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x130004c00004cf01300f))) = true := by
  decide +kernel

end CDCert.K6
