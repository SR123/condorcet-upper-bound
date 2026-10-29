/-
CDCert.K6.Six.F029 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 442, 656, 657, 704, 764, 768, 783, 815, 879, 1019, 1054, 1059, 1102, 1148.
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

theorem six_rep_442 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70410d7))) = true := by
  decide +kernel

theorem six_rep_656 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c70014c7))) = true := by
  decide +kernel

theorem six_rep_657 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c702d007))) = true := by
  decide +kernel

theorem six_rep_704 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14c70014c7))) = true := by
  decide +kernel

theorem six_rep_764 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100302d08306d))) = true := by
  decide +kernel

theorem six_rep_768 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101300d01304d))) = true := by
  decide +kernel

theorem six_rep_783 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108302d00306d))) = true := by
  decide +kernel

theorem six_rep_815 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x300300f0130cf))) = true := by
  decide +kernel

theorem six_rep_879 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x508302d00016d))) = true := by
  decide +kernel

theorem six_rep_1019 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf04001300c3d3))) = true := by
  decide +kernel

theorem six_rep_1054 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2d00300d000b4d))) = true := by
  decide +kernel

theorem six_rep_1059 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70041c01005c0))) = true := by
  decide +kernel

theorem six_rep_1102 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10004c00004d7001017))) = true := by
  decide +kernel

theorem six_rep_1148 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100004001c04304d0030))) = true := by
  decide +kernel

end CDCert.K6
