/-
CDCert.K6.Six.F038 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 583, 631, 641, 644, 660, 707, 708, 996, 1009, 1076, 1157.
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

theorem six_rep_583 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d08306d))) = true := by
  decide +kernel

theorem six_rep_631 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d7000cd7))) = true := by
  decide +kernel

theorem six_rep_641 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f30005f3))) = true := by
  decide +kernel

theorem six_rep_644 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f34c00f3))) = true := by
  decide +kernel

theorem six_rep_660 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c71014c7))) = true := by
  decide +kernel

theorem six_rep_707 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14c71014c7))) = true := by
  decide +kernel

theorem six_rep_708 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14c7300cc7))) = true := by
  decide +kernel

theorem six_rep_996 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc41300c00f30c))) = true := by
  decide +kernel

theorem six_rep_1009 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd41300d00034d))) = true := by
  decide +kernel

theorem six_rep_1076 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10070400130441d3))) = true := by
  decide +kernel

theorem six_rep_1157 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000400000030010170400d7))) = true := by
  decide +kernel

end CDCert.K6
