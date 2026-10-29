/-
CDCert.K6.Six.F023 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 360, 405, 417, 562, 603, 694, 790, 882, 991, 1024, 1040, 1053, 1057, 1098, 1104, 1113, 1118.
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

theorem six_rep_360 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d01306d))) = true := by
  decide +kernel

theorem six_rep_405 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c7300cc7))) = true := by
  decide +kernel

theorem six_rep_417 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf01700f))) = true := by
  decide +kernel

theorem six_rep_562 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34582d005))) = true := by
  decide +kernel

theorem six_rep_603 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c7000cc7))) = true := by
  decide +kernel

theorem six_rep_694 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10c71014c7))) = true := by
  decide +kernel

theorem six_rep_790 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x141300d00304d))) = true := by
  decide +kernel

theorem six_rep_882 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x541300d00014d))) = true := by
  decide +kernel

theorem six_rep_991 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc08002c00f32c))) = true := by
  decide +kernel

theorem six_rep_1024 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x170000170005d7))) = true := by
  decide +kernel

theorem six_rep_1040 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2801200803aa08))) = true := by
  decide +kernel

theorem six_rep_1053 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2d001005200b45))) = true := by
  decide +kernel

theorem six_rep_1057 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d004140200b40))) = true := by
  decide +kernel

theorem six_rep_1098 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000c00000d7041017))) = true := by
  decide +kernel

theorem six_rep_1104 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10004c01004c7001007))) = true := by
  decide +kernel

theorem six_rep_1113 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000020c003a0020ba))) = true := by
  decide +kernel

theorem six_rep_1118 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200001200003a0024ba))) = true := by
  decide +kernel

end CDCert.K6
