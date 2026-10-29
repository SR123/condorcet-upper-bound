/-
CDCert.K6.Six.F030 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 434, 564, 573, 697, 817, 864, 865, 896, 898, 1003, 1026, 1072, 1073.
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

theorem six_rep_434 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d70005d7))) = true := by
  decide +kernel

theorem six_rep_564 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d000b4d))) = true := by
  decide +kernel

theorem six_rep_573 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34dc3300d))) = true := by
  decide +kernel

theorem six_rep_697 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d70014d7))) = true := by
  decide +kernel

theorem six_rep_817 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x301300f0030cf))) = true := by
  decide +kernel

theorem six_rep_864 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x448002c01712c))) = true := by
  decide +kernel

theorem six_rep_865 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x448002c08712c))) = true := by
  decide +kernel

theorem six_rep_896 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70010170401d7))) = true := by
  decide +kernel

theorem six_rep_898 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x701300f0001cf))) = true := by
  decide +kernel

theorem six_rep_1003 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd00302d00036d))) = true := by
  decide +kernel

theorem six_rep_1026 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x170010071005c7))) = true := by
  decide +kernel

theorem six_rep_1072 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100408002c01712c))) = true := by
  decide +kernel

theorem six_rep_1073 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100408002c08712c))) = true := by
  decide +kernel

end CDCert.K6
