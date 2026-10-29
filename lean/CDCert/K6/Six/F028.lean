/-
CDCert.K6.Six.F028 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 440, 600, 602, 606, 614, 699, 717, 812, 820, 909, 986, 1047, 1060, 1088.
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

theorem six_rep_440 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70401d7))) = true := by
  decide +kernel

theorem six_rep_600 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c3b00cc3))) = true := by
  decide +kernel

theorem six_rep_602 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c70005c7))) = true := by
  decide +kernel

theorem six_rep_606 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c702d007))) = true := by
  decide +kernel

theorem six_rep_614 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf0030cf))) = true := by
  decide +kernel

theorem six_rep_699 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d70401d7))) = true := by
  decide +kernel

theorem six_rep_717 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20ba0c20ba))) = true := by
  decide +kernel

theorem six_rep_812 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30010170410d7))) = true := by
  decide +kernel

theorem six_rep_820 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30410170010d7))) = true := by
  decide +kernel

theorem six_rep_909 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x74c00330001f3))) = true := by
  decide +kernel

theorem six_rep_986 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc00302c00f32c))) = true := by
  decide +kernel

theorem six_rep_1047 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2c00300c00fb0c))) = true := by
  decide +kernel

theorem six_rep_1060 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f30041c0300cc0))) = true := by
  decide +kernel

theorem six_rep_1088 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000030000170410d7))) = true := by
  decide +kernel

end CDCert.K6
