/-
CDCert.K6.Six.F033 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 576, 581, 609, 627, 645, 652, 722, 797, 843, 1004, 1125, 1137.
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

theorem six_rep_576 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d00f02d))) = true := by
  decide +kernel

theorem six_rep_581 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d08016d))) = true := by
  decide +kernel

theorem six_rep_609 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c71014c7))) = true := by
  decide +kernel

theorem six_rep_627 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30441d3))) = true := by
  decide +kernel

theorem six_rep_645 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f35c0033))) = true := by
  decide +kernel

theorem six_rep_652 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c302c3c3))) = true := by
  decide +kernel

theorem six_rep_722 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30cf0034cf))) = true := by
  decide +kernel

theorem six_rep_797 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x148002d48006d))) = true := by
  decide +kernel

theorem six_rep_843 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401300c41710c))) = true := by
  decide +kernel

theorem six_rep_1004 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd01300d00034d))) = true := by
  decide +kernel

theorem six_rep_1125 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20004001c04380c2038))) = true := by
  decide +kernel

theorem six_rep_1137 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x21004800004ba00203a))) = true := by
  decide +kernel

end CDCert.K6
