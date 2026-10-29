/-
CDCert.K6.Six.F032 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 571, 574, 619, 654, 668, 687, 701, 860, 904, 988, 1015, 1022, 1141.
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

theorem six_rep_571 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d41304d))) = true := by
  decide +kernel

theorem six_rep_574 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d00036d))) = true := by
  decide +kernel

theorem six_rep_619 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf03300f))) = true := by
  decide +kernel

theorem six_rep_654 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c70005c7))) = true := by
  decide +kernel

theorem six_rep_668 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5d70010d7))) = true := by
  decide +kernel

theorem six_rep_687 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xb4d01304d))) = true := by
  decide +kernel

theorem six_rep_701 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d70410d7))) = true := by
  decide +kernel

theorem six_rep_860 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x441300c01710c))) = true := by
  decide +kernel

theorem six_rep_904 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70400170401d7))) = true := by
  decide +kernel

theorem six_rep_988 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc01300c00f30c))) = true := by
  decide +kernel

theorem six_rep_1015 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf0010170003d7))) = true := by
  decide +kernel

theorem six_rep_1022 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf0c00330003f3))) = true := by
  decide +kernel

theorem six_rep_1141 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30004c00004cf00300f))) = true := by
  decide +kernel

end CDCert.K6
