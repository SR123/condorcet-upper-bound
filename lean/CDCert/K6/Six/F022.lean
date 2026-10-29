/-
CDCert.K6.Six.F022 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 361, 367, 414, 424, 443, 593, 686, 759, 793, 838, 883, 973, 975, 1002, 1075, 1083, 1126.
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

theorem six_rep_361 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d01702d))) = true := by
  decide +kernel

theorem six_rep_367 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d08702d))) = true := by
  decide +kernel

theorem six_rep_414 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf00f00f))) = true := by
  decide +kernel

theorem six_rep_424 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d30045d3))) = true := by
  decide +kernel

theorem six_rep_443 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d7045017))) = true := by
  decide +kernel

theorem six_rep_593 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c30045c3))) = true := by
  decide +kernel

theorem six_rep_686 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xb4d00304d))) = true := by
  decide +kernel

theorem six_rep_759 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100300d41304d))) = true := by
  decide +kernel

theorem six_rep_793 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x148002d00306d))) = true := by
  decide +kernel

theorem six_rep_838 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x400302c01712c))) = true := by
  decide +kernel

theorem six_rep_883 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x548002d00016d))) = true := by
  decide +kernel

theorem six_rep_973 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x8480020cb8220))) = true := by
  decide +kernel

theorem six_rep_975 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x848002803a228))) = true := by
  decide +kernel

theorem six_rep_1002 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd00300d00034d))) = true := by
  decide +kernel

theorem six_rep_1075 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10070400130041d3))) = true := by
  decide +kernel

theorem six_rep_1083 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200808002803a228))) = true := by
  decide +kernel

theorem six_rep_1126 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20004800004ba00203a))) = true := by
  decide +kernel

end CDCert.K6
