/-
CDCert.K6.Six.F020 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 358, 364, 428, 438, 452, 555, 582, 597, 599, 607, 620, 622, 636, 836, 844, 966, 985, 1012, 1121.
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

theorem six_rep_358 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d00f02d))) = true := by
  decide +kernel

theorem six_rep_364 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d08016d))) = true := by
  decide +kernel

theorem six_rep_428 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d30441d3))) = true := by
  decide +kernel

theorem six_rep_438 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d700d017))) = true := by
  decide +kernel

theorem six_rep_452 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f33c0033))) = true := by
  decide +kernel

theorem six_rep_555 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x341a00b41))) = true := by
  decide +kernel

theorem six_rep_582 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d08302d))) = true := by
  decide +kernel

theorem six_rep_597 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c31005c3))) = true := by
  decide +kernel

theorem six_rep_599 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c3300cc3))) = true := by
  decide +kernel

theorem six_rep_607 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c71004c7))) = true := by
  decide +kernel

theorem six_rep_620 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30003d3))) = true := by
  decide +kernel

theorem six_rep_622 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30041d3))) = true := by
  decide +kernel

theorem six_rep_636 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d7041017))) = true := by
  decide +kernel

theorem six_rep_836 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x400300c41710c))) = true := by
  decide +kernel

theorem six_rep_844 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401302c00712c))) = true := by
  decide +kernel

theorem six_rep_966 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x841200803a208))) = true := by
  decide +kernel

theorem six_rep_985 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc00300c00f30c))) = true := by
  decide +kernel

theorem six_rep_1012 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf0000170003d7))) = true := by
  decide +kernel

theorem six_rep_1121 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000800000ba0c203a))) = true := by
  decide +kernel

end CDCert.K6
