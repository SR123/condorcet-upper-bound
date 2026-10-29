/-
CDCert.K6.Six.F034 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 584, 613, 638, 639, 640, 732, 846, 1016, 1110, 1139, 1150, 1158.
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

theorem six_rep_584 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d08702d))) = true := by
  decide +kernel

theorem six_rep_613 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf000ccf))) = true := by
  decide +kernel

theorem six_rep_638 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d7045017))) = true := by
  decide +kernel

theorem six_rep_639 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d7141017))) = true := by
  decide +kernel

theorem six_rep_640 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f30003f3))) = true := by
  decide +kernel

theorem six_rep_732 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x45c3300cc3))) = true := by
  decide +kernel

theorem six_rep_846 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401302c08712c))) = true := by
  decide +kernel

theorem six_rep_1016 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf00300f0003cf))) = true := by
  decide +kernel

theorem six_rep_1110 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x11004c01004c7001007))) = true := by
  decide +kernel

theorem six_rep_1139 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x300001300000f0034cf))) = true := by
  decide +kernel

theorem six_rep_1150 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100004800004b24d0032))) = true := by
  decide +kernel

theorem six_rep_1158 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10001000001c00041d3040013))) = true := by
  decide +kernel

end CDCert.K6
