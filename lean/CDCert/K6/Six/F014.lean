/-
CDCert.K6.Six.F014 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 201, 234, 252, 325, 339, 341, 384, 397, 408, 413, 421, 446, 548, 700, 752, 782, 811, 816, 869, 877, 900, 923, 925, 1033, 1097.
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

theorem six_rep_201 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x6d08306d))) = true := by
  decide +kernel

theorem six_rep_234 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc7300cc7))) = true := by
  decide +kernel

theorem six_rep_252 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd70003d7))) = true := by
  decide +kernel

theorem six_rep_325 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14182c341))) = true := by
  decide +kernel

theorem six_rep_339 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14582d005))) = true := by
  decide +kernel

theorem six_rep_341 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d00034d))) = true := by
  decide +kernel

theorem six_rep_384 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c300c3c3))) = true := by
  decide +kernel

theorem six_rep_397 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c7000cc7))) = true := by
  decide +kernel

theorem six_rep_408 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf0004cf))) = true := by
  decide +kernel

theorem six_rep_413 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf00700f))) = true := by
  decide +kernel

theorem six_rep_421 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d30005d3))) = true := by
  decide +kernel

theorem six_rep_446 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f30001f3))) = true := by
  decide +kernel

theorem six_rep_548 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x341200b41))) = true := by
  decide +kernel

theorem six_rep_700 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10d7041017))) = true := by
  decide +kernel

theorem six_rep_752 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100002d08306d))) = true := by
  decide +kernel

theorem six_rep_782 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108302d00006d))) = true := by
  decide +kernel

theorem six_rep_811 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30010170400d7))) = true := by
  decide +kernel

theorem six_rep_816 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x301300f0000cf))) = true := by
  decide +kernel

theorem six_rep_869 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x500002d08016d))) = true := by
  decide +kernel

theorem six_rep_877 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x508002d00016d))) = true := by
  decide +kernel

theorem six_rep_900 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70400130041d3))) = true := by
  decide +kernel

theorem six_rep_923 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x8002008c3a208))) = true := by
  decide +kernel

theorem six_rep_925 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x800202803a228))) = true := by
  decide +kernel

theorem six_rep_1033 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2800200803aa08))) = true := by
  decide +kernel

theorem six_rep_1097 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000c00000d7001017))) = true := by
  decide +kernel

end CDCert.K6
