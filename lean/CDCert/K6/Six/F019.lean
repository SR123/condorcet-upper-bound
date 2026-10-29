/-
CDCert.K6.Six.F019 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 351, 352, 355, 369, 386, 389, 418, 445, 546, 557, 560, 580, 781, 795, 874, 893, 897, 1014, 1044, 1045.
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

theorem six_rep_351 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d41304d))) = true := by
  decide +kernel

theorem six_rep_352 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14d41700d))) = true := by
  decide +kernel

theorem six_rep_355 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d00036d))) = true := by
  decide +kernel

theorem six_rep_369 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x16d48006d))) = true := by
  decide +kernel

theorem six_rep_386 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c302c3c3))) = true := by
  decide +kernel

theorem six_rep_389 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c31045c3))) = true := by
  decide +kernel

theorem six_rep_418 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf03300f))) = true := by
  decide +kernel

theorem six_rep_445 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d7340017))) = true := by
  decide +kernel

theorem six_rep_546 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34102c341))) = true := by
  decide +kernel

theorem six_rep_557 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x345000b45))) = true := by
  decide +kernel

theorem six_rep_560 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34502d005))) = true := by
  decide +kernel

theorem six_rep_580 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d08006d))) = true := by
  decide +kernel

theorem six_rep_781 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108002d48006d))) = true := by
  decide +kernel

theorem six_rep_795 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x148002d08006d))) = true := by
  decide +kernel

theorem six_rep_874 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x501300d00014d))) = true := by
  decide +kernel

theorem six_rep_893 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70000330c01f3))) = true := by
  decide +kernel

theorem six_rep_897 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x700300f0001cf))) = true := by
  decide +kernel

theorem six_rep_1014 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf0010070003c7))) = true := by
  decide +kernel

theorem six_rep_1044 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2c00100402db04))) = true := by
  decide +kernel

theorem six_rep_1045 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2c00100420db04))) = true := by
  decide +kernel

end CDCert.K6
