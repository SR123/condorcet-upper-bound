/-
CDCert.K6.Six.F035 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 577, 578, 616, 623, 731, 738, 775, 791, 794, 908, 1145.
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

theorem six_rep_577 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d01306d))) = true := by
  decide +kernel

theorem six_rep_578 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d01702d))) = true := by
  decide +kernel

theorem six_rep_616 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf00f00f))) = true := by
  decide +kernel

theorem six_rep_623 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30045d3))) = true := by
  decide +kernel

theorem six_rep_731 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x45c31005c3))) = true := by
  decide +kernel

theorem six_rep_738 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc3c3300cc3))) = true := by
  decide +kernel

theorem six_rep_775 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101302d48006d))) = true := by
  decide +kernel

theorem six_rep_791 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x141300d01304d))) = true := by
  decide +kernel

theorem six_rep_794 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x148002d01306d))) = true := by
  decide +kernel

theorem six_rep_908 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70c00330c01f3))) = true := by
  decide +kernel

theorem six_rep_1145 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100000100c00305d0430))) = true := by
  decide +kernel

end CDCert.K6
