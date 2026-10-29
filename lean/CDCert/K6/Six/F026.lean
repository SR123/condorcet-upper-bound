/-
CDCert.K6.Six.F026 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 366, 409, 416, 432, 547, 549, 567, 568, 650, 711, 762, 780, 1089, 1092, 1099, 1112.
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

theorem six_rep_366 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d08306d))) = true := by
  decide +kernel

theorem six_rep_409 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0005cf))) = true := by
  decide +kernel

theorem six_rep_416 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0130cf))) = true := by
  decide +kernel

theorem six_rep_432 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70003d7))) = true := by
  decide +kernel

theorem six_rep_547 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34102cb41))) = true := by
  decide +kernel

theorem six_rep_549 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34120cb41))) = true := by
  decide +kernel

theorem six_rep_567 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d01304d))) = true := by
  decide +kernel

theorem six_rep_568 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d01700d))) = true := by
  decide +kernel

theorem six_rep_650 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c30045c3))) = true := by
  decide +kernel

theorem six_rep_711 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d7041017))) = true := by
  decide +kernel

theorem six_rep_762 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100302d01306d))) = true := by
  decide +kernel

theorem six_rep_780 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108002d08306d))) = true := by
  decide +kernel

theorem six_rep_1089 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000030400170010d7))) = true := by
  decide +kernel

theorem six_rep_1092 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000130000071014c7))) = true := by
  decide +kernel

theorem six_rep_1099 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000c00400d7001017))) = true := by
  decide +kernel

theorem six_rep_1112 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200000200003a0c20ba))) = true := by
  decide +kernel

end CDCert.K6
