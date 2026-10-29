/-
CDCert.K6.Six.F027 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 412, 437, 451, 561, 586, 632, 634, 642, 651, 771, 842, 873, 875, 1105, 1136.
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

theorem six_rep_412 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0034cf))) = true := by
  decide +kernel

theorem six_rep_437 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70014d7))) = true := by
  decide +kernel

theorem six_rep_451 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f30c01f3))) = true := by
  decide +kernel

theorem six_rep_561 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x345200b45))) = true := by
  decide +kernel

theorem six_rep_586 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36dc8002d))) = true := by
  decide +kernel

theorem six_rep_632 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70010d7))) = true := by
  decide +kernel

theorem six_rep_634 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70400d7))) = true := by
  decide +kernel

theorem six_rep_642 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f30c00f3))) = true := by
  decide +kernel

theorem six_rep_651 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c300c3c3))) = true := by
  decide +kernel

theorem six_rep_771 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101302d00306d))) = true := by
  decide +kernel

theorem six_rep_842 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401300c01710c))) = true := by
  decide +kernel

theorem six_rep_873 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x500302d08016d))) = true := by
  decide +kernel

theorem six_rep_875 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x501302d00016d))) = true := by
  decide +kernel

theorem six_rep_1105 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10400130000070014c7))) = true := by
  decide +kernel

theorem six_rep_1136 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x21004001c0438002038))) = true := by
  decide +kernel

end CDCert.K6
