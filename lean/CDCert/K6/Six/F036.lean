/-
CDCert.K6.Six.F036 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 610, 618, 653, 769, 845, 998, 1027, 1028, 1074, 1117, 1132.
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

theorem six_rep_610 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c7300cc7))) = true := by
  decide +kernel

theorem six_rep_618 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf01700f))) = true := by
  decide +kernel

theorem six_rep_653 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c31045c3))) = true := by
  decide +kernel

theorem six_rep_769 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101300d41304d))) = true := by
  decide +kernel

theorem six_rep_845 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x401302c01712c))) = true := by
  decide +kernel

theorem six_rep_998 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc48002c00f32c))) = true := by
  decide +kernel

theorem six_rep_1027 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x170010170005d7))) = true := by
  decide +kernel

theorem six_rep_1028 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1700300f0005cf))) = true := by
  decide +kernel

theorem six_rep_1074 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100508002d08016d))) = true := by
  decide +kernel

theorem six_rep_1117 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000100c00381c2438))) = true := by
  decide +kernel

theorem six_rep_1132 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x204001200003a0024ba))) = true := by
  decide +kernel

end CDCert.K6
