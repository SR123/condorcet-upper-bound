/-
CDCert.K6.Six.F024 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 403, 407, 425, 553, 563, 594, 621, 658, 683, 685, 693, 695, 703, 878, 933, 935.
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

theorem six_rep_403 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c71005c7))) = true := by
  decide +kernel

theorem six_rep_407 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0003cf))) = true := by
  decide +kernel

theorem six_rep_425 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d300c3d3))) = true := by
  decide +kernel

theorem six_rep_553 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34182c341))) = true := by
  decide +kernel

theorem six_rep_563 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d00034d))) = true := by
  decide +kernel

theorem six_rep_594 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c300c3c3))) = true := by
  decide +kernel

theorem six_rep_621 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30005d3))) = true := by
  decide +kernel

theorem six_rep_658 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c71004c7))) = true := by
  decide +kernel

theorem six_rep_683 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xb4102c341))) = true := by
  decide +kernel

theorem six_rep_685 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xb4502d005))) = true := by
  decide +kernel

theorem six_rep_693 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10c71005c7))) = true := by
  decide +kernel

theorem six_rep_695 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10c7300cc7))) = true := by
  decide +kernel

theorem six_rep_703 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d7141017))) = true := by
  decide +kernel

theorem six_rep_878 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x508002d08016d))) = true := by
  decide +kernel

theorem six_rep_933 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x8012008c3a208))) = true := by
  decide +kernel

theorem six_rep_935 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x801202803a228))) = true := by
  decide +kernel

end CDCert.K6
