/-
CDCert.K6.Six.F015 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 239, 247, 255, 317, 345, 348, 356, 394, 399, 406, 430, 433, 544, 559, 590, 649, 803, 819, 841, 889, 901, 979, 982, 1087.
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

theorem six_rep_239 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xcf0005cf))) = true := by
  decide +kernel

theorem six_rep_247 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xcf0130cf))) = true := by
  decide +kernel

theorem six_rep_255 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd70014d7))) = true := by
  decide +kernel

theorem six_rep_317 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14102cb41))) = true := by
  decide +kernel

theorem six_rep_345 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d00f00d))) = true := by
  decide +kernel

theorem six_rep_348 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d01700d))) = true := by
  decide +kernel

theorem six_rep_356 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d00306d))) = true := by
  decide +kernel

theorem six_rep_394 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c70003c7))) = true := by
  decide +kernel

theorem six_rep_399 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c70014c7))) = true := by
  decide +kernel

theorem six_rep_406 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0001cf))) = true := by
  decide +kernel

theorem six_rep_430 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d3b40013))) = true := by
  decide +kernel

theorem six_rep_433 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70004d7))) = true := by
  decide +kernel

theorem six_rep_544 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34100c341))) = true := by
  decide +kernel

theorem six_rep_559 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34500d005))) = true := by
  decide +kernel

theorem six_rep_590 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c30005c3))) = true := by
  decide +kernel

theorem six_rep_649 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c30041c3))) = true := by
  decide +kernel

theorem six_rep_803 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x300000f0130cf))) = true := by
  decide +kernel

theorem six_rep_819 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30410170000d7))) = true := by
  decide +kernel

theorem six_rep_841 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401300c00710c))) = true := by
  decide +kernel

theorem six_rep_889 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70000130441d3))) = true := by
  decide +kernel

theorem six_rep_901 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70400130401d3))) = true := by
  decide +kernel

theorem six_rep_979 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc00002c00f32c))) = true := by
  decide +kernel

theorem six_rep_982 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc00100402d304))) = true := by
  decide +kernel

theorem six_rep_1087 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000030000170010d7))) = true := by
  decide +kernel

end CDCert.K6
