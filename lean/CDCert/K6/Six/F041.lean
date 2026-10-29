/-
CDCert.K6.Six.F041 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 633, 635, 659, 661, 665, 989, 1055, 1100, 1119, 1122.
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

theorem six_rep_633 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70014d7))) = true := by
  decide +kernel

theorem six_rep_635 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70401d7))) = true := by
  decide +kernel

theorem six_rep_659 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c71005c7))) = true := by
  decide +kernel

theorem six_rep_661 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c7300cc7))) = true := by
  decide +kernel

theorem six_rep_665 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5cf0130cf))) = true := by
  decide +kernel

theorem six_rep_989 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc01302c00f32c))) = true := by
  decide +kernel

theorem six_rep_1055 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2d01300d000b4d))) = true := by
  decide +kernel

theorem six_rep_1100 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000c00400d7041017))) = true := by
  decide +kernel

theorem six_rep_1119 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000120c003a0024ba))) = true := by
  decide +kernel

theorem six_rep_1122 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000800c00ba0c203a))) = true := by
  decide +kernel

end CDCert.K6
