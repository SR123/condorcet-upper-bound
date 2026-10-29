/-
CDCert.K6.Six.F039 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 612, 617, 629, 672, 706, 787, 796, 1106, 1109, 1152.
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

theorem six_rep_612 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf0005cf))) = true := by
  decide +kernel

theorem six_rep_617 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3cf0130cf))) = true := by
  decide +kernel

theorem six_rep_629 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70003d7))) = true := by
  decide +kernel

theorem six_rep_672 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5d7045017))) = true := by
  decide +kernel

theorem six_rep_706 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14c71005c7))) = true := by
  decide +kernel

theorem six_rep_787 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108302d48006d))) = true := by
  decide +kernel

theorem six_rep_796 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x148002d08306d))) = true := by
  decide +kernel

theorem six_rep_1106 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10400130000071014c7))) = true := by
  decide +kernel

theorem six_rep_1109 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x11004c00004d7001017))) = true := by
  decide +kernel

theorem six_rep_1152 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x120004800004ba01203a))) = true := by
  decide +kernel

end CDCert.K6
