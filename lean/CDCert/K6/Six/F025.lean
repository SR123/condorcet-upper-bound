/-
CDCert.K6.Six.F025 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 435, 448, 454, 566, 575, 601, 605, 628, 670, 702, 737, 785, 902, 950, 1006, 1108.
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

theorem six_rep_435 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d7000cd7))) = true := by
  decide +kernel

theorem six_rep_448 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f30005f3))) = true := by
  decide +kernel

theorem six_rep_454 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f34c00f3))) = true := by
  decide +kernel

theorem six_rep_566 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d00f00d))) = true := by
  decide +kernel

theorem six_rep_575 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d00306d))) = true := by
  decide +kernel

theorem six_rep_601 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c70003c7))) = true := by
  decide +kernel

theorem six_rep_605 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c70014c7))) = true := by
  decide +kernel

theorem six_rep_628 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d3b40013))) = true := by
  decide +kernel

theorem six_rep_670 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5d7041017))) = true := by
  decide +kernel

theorem six_rep_702 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d7045017))) = true := by
  decide +kernel

theorem six_rep_737 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x8e82300c82))) = true := by
  decide +kernel

theorem six_rep_785 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108302d08006d))) = true := by
  decide +kernel

theorem six_rep_902 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70400130441d3))) = true := by
  decide +kernel

theorem six_rep_950 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x808202803a228))) = true := by
  decide +kernel

theorem six_rep_1006 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd08002d00036d))) = true := by
  decide +kernel

theorem six_rep_1108 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x11004c00004c7001007))) = true := by
  decide +kernel

end CDCert.K6
