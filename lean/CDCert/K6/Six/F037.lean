/-
CDCert.K6.Six.F037 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 608, 611, 624, 666, 718, 719, 853, 854, 884, 1010, 1155.
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

theorem six_rep_608 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c71005c7))) = true := by
  decide +kernel

theorem six_rep_611 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf0003cf))) = true := by
  decide +kernel

theorem six_rep_624 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d300c3d3))) = true := by
  decide +kernel

theorem six_rep_666 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5cf01700f))) = true := by
  decide +kernel

theorem six_rep_718 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x24ba0024ba))) = true := by
  decide +kernel

theorem six_rep_719 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x24ba0120ba))) = true := by
  decide +kernel

theorem six_rep_853 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x408302c01712c))) = true := by
  decide +kernel

theorem six_rep_854 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x408302c08712c))) = true := by
  decide +kernel

theorem six_rep_884 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x548002d08016d))) = true := by
  decide +kernel

theorem six_rep_1010 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd48002d00036d))) = true := by
  decide +kernel

theorem six_rep_1155 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000010000c00000d7041017))) = true := by
  decide +kernel

end CDCert.K6
