/-
CDCert.K6.Six.F012 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 192, 233, 240, 249, 257, 260, 316, 327, 331, 335, 354, 359, 363, 365, 388, 390, 400, 402, 415, 420, 422, 423, 453, 692, 727, 837, 871, 999.
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

theorem six_rep_192 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x6d00f02d))) = true := by
  decide +kernel

theorem six_rep_233 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc71014c7))) = true := by
  decide +kernel

theorem six_rep_240 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xcf000ccf))) = true := by
  decide +kernel

theorem six_rep_249 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xcf03300f))) = true := by
  decide +kernel

theorem six_rep_257 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd700d017))) = true := by
  decide +kernel

theorem six_rep_260 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd7045017))) = true := by
  decide +kernel

theorem six_rep_316 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14102c341))) = true := by
  decide +kernel

theorem six_rep_327 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x141a00b41))) = true := by
  decide +kernel

theorem six_rep_331 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x145000b45))) = true := by
  decide +kernel

theorem six_rep_335 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14502d005))) = true := by
  decide +kernel

theorem six_rep_354 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d00016d))) = true := by
  decide +kernel

theorem six_rep_359 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d01302d))) = true := by
  decide +kernel

theorem six_rep_363 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d08006d))) = true := by
  decide +kernel

theorem six_rep_365 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d08302d))) = true := by
  decide +kernel

theorem six_rep_388 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c31005c3))) = true := by
  decide +kernel

theorem six_rep_390 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c3300cc3))) = true := by
  decide +kernel

theorem six_rep_400 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c700d007))) = true := by
  decide +kernel

theorem six_rep_402 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c71004c7))) = true := by
  decide +kernel

theorem six_rep_415 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf01300f))) = true := by
  decide +kernel

theorem six_rep_420 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d30003d3))) = true := by
  decide +kernel

theorem six_rep_422 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d3000cd3))) = true := by
  decide +kernel

theorem six_rep_423 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d30041d3))) = true := by
  decide +kernel

theorem six_rep_453 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f34c0033))) = true := by
  decide +kernel

theorem six_rep_692 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10c71004c7))) = true := by
  decide +kernel

theorem six_rep_727 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x4141200b41))) = true := by
  decide +kernel

theorem six_rep_837 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x400302c00712c))) = true := by
  decide +kernel

theorem six_rep_871 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x500300d00014d))) = true := by
  decide +kernel

theorem six_rep_999 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd00000d00034d))) = true := by
  decide +kernel

end CDCert.K6
