/-
CDCert.K6.Six.F018 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 342, 353, 362, 456, 545, 655, 682, 696, 729, 730, 767, 814, 859, 891, 895, 983, 1011, 1116, 1138, 1144.
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

theorem six_rep_342 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d000b4d))) = true := by
  decide +kernel

theorem six_rep_353 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14dc3300d))) = true := by
  decide +kernel

theorem six_rep_362 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d03302d))) = true := by
  decide +kernel

theorem six_rep_456 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f3cc0033))) = true := by
  decide +kernel

theorem six_rep_545 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34100cb41))) = true := by
  decide +kernel

theorem six_rep_655 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5c70010c7))) = true := by
  decide +kernel

theorem six_rep_682 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xb4100c341))) = true := by
  decide +kernel

theorem six_rep_696 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d70010d7))) = true := by
  decide +kernel

theorem six_rep_729 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x41c31005c3))) = true := by
  decide +kernel

theorem six_rep_730 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x41c3300cc3))) = true := by
  decide +kernel

theorem six_rep_767 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101300d00304d))) = true := by
  decide +kernel

theorem six_rep_814 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x300300f0030cf))) = true := by
  decide +kernel

theorem six_rep_859 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x441300c00710c))) = true := by
  decide +kernel

theorem six_rep_891 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70000170401d7))) = true := by
  decide +kernel

theorem six_rep_895 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70010170001d7))) = true := by
  decide +kernel

theorem six_rep_983 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc00100482d304))) = true := by
  decide +kernel

theorem six_rep_1011 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf00000f0003cf))) = true := by
  decide +kernel

theorem six_rep_1116 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20000100000381c2438))) = true := by
  decide +kernel

theorem six_rep_1138 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x300000300000f0030cf))) = true := by
  decide +kernel

theorem six_rep_1144 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100000100000305d0430))) = true := by
  decide +kernel

end CDCert.K6
