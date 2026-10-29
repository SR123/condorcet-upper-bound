/-
CDCert.K6.Six.F040 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 615, 643, 713, 714, 772, 876, 1051, 1084, 1127, 1156.
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

theorem six_rep_615 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf0034cf))) = true := by
  decide +kernel

theorem six_rep_643 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f30c01f3))) = true := by
  decide +kernel

theorem six_rep_713 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d7045017))) = true := by
  decide +kernel

theorem six_rep_714 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d7141017))) = true := by
  decide +kernel

theorem six_rep_772 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101302d01306d))) = true := by
  decide +kernel

theorem six_rep_876 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x501302d08016d))) = true := by
  decide +kernel

theorem six_rep_1051 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2c01300c00fb0c))) = true := by
  decide +kernel

theorem six_rep_1084 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20380c00303c0e30))) = true := by
  decide +kernel

theorem six_rep_1127 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20004800004ba0c203a))) = true := by
  decide +kernel

theorem six_rep_1156 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000040000070000130441d3))) = true := by
  decide +kernel

end CDCert.K6
