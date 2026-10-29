/-
CDCert.K6.Six.F043 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 630, 662, 720, 1007, 1023, 1077, 1090, 1094, 1154.
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

theorem six_rep_630 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70005d7))) = true := by
  decide +kernel

theorem six_rep_662 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5cf0005cf))) = true := by
  decide +kernel

theorem six_rep_720 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x24ba0c20ba))) = true := by
  decide +kernel

theorem six_rep_1007 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd08302d00036d))) = true := by
  decide +kernel

theorem six_rep_1023 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf4c00330003f3))) = true := by
  decide +kernel

theorem six_rep_1077 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10070400170401d7))) = true := by
  decide +kernel

theorem six_rep_1090 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000030400170410d7))) = true := by
  decide +kernel

theorem six_rep_1094 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000130400170014d7))) = true := by
  decide +kernel

theorem six_rep_1154 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000010000030000170410d7))) = true := by
  decide +kernel

end CDCert.K6
