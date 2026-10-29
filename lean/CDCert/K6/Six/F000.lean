/-
CDCert.K6.Six.F000 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 23, 24, 25, 26, 33, 39, 45, 46, 53, 56, 59, 61, 68, 69, 79, 87, 126, 127, 128, 130, 131, 132, 134, 206, 208, 261, 262, 263, 265, 266, 276, 282, 283, 286, 289, 290, 457, 458, 459, 461, 464, 470, 478, 481, 482.
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

theorem six_rep_0 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1))) = true := by
  decide +kernel

theorem six_rep_1 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3))) = true := by
  decide +kernel

theorem six_rep_2 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5))) = true := by
  decide +kernel

theorem six_rep_3 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x7))) = true := by
  decide +kernel

theorem six_rep_4 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf))) = true := by
  decide +kernel

theorem six_rep_5 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x17))) = true := by
  decide +kernel

theorem six_rep_6 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x41))) = true := by
  decide +kernel

theorem six_rep_7 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x45))) = true := by
  decide +kernel

theorem six_rep_8 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x4d))) = true := by
  decide +kernel

theorem six_rep_9 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x6d))) = true := by
  decide +kernel

theorem six_rep_10 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc3))) = true := by
  decide +kernel

theorem six_rep_11 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc7))) = true := by
  decide +kernel

theorem six_rep_12 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xcf))) = true := by
  decide +kernel

theorem six_rep_14 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x120))) = true := by
  decide +kernel

theorem six_rep_15 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x145))) = true := by
  decide +kernel

theorem six_rep_23 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x208))) = true := by
  decide +kernel

theorem six_rep_24 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x220))) = true := by
  decide +kernel

theorem six_rep_25 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x228))) = true := by
  decide +kernel

theorem six_rep_26 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x230))) = true := by
  decide +kernel

theorem six_rep_33 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1045))) = true := by
  decide +kernel

theorem six_rep_39 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2408))) = true := by
  decide +kernel

theorem six_rep_45 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1000001))) = true := by
  decide +kernel

theorem six_rep_46 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1000041))) = true := by
  decide +kernel

theorem six_rep_53 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1020001))) = true := by
  decide +kernel

theorem six_rep_56 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1200001))) = true := by
  decide +kernel

theorem six_rep_59 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1400001))) = true := by
  decide +kernel

theorem six_rep_61 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1800001))) = true := by
  decide +kernel

theorem six_rep_68 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3000003))) = true := by
  decide +kernel

theorem six_rep_69 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30000c3))) = true := by
  decide +kernel

theorem six_rep_79 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5000005))) = true := by
  decide +kernel

theorem six_rep_87 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x7000007))) = true := by
  decide +kernel

theorem six_rep_126 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40004000))) = true := by
  decide +kernel

theorem six_rep_127 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x4000c000))) = true := by
  decide +kernel

theorem six_rep_128 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40020000))) = true := by
  decide +kernel

theorem six_rep_130 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40200000))) = true := by
  decide +kernel

theorem six_rep_131 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40800000))) = true := by
  decide +kernel

theorem six_rep_132 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40820000))) = true := by
  decide +kernel

theorem six_rep_134 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x40a00000))) = true := by
  decide +kernel

theorem six_rep_206 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc0004000))) = true := by
  decide +kernel

theorem six_rep_208 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc0020000))) = true := by
  decide +kernel

theorem six_rep_261 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100000100))) = true := by
  decide +kernel

theorem six_rep_262 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100000300))) = true := by
  decide +kernel

theorem six_rep_263 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100000800))) = true := by
  decide +kernel

theorem six_rep_265 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100004000))) = true := by
  decide +kernel

theorem six_rep_266 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100004100))) = true := by
  decide +kernel

theorem six_rep_276 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100020000))) = true := by
  decide +kernel

theorem six_rep_282 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100200000))) = true := by
  decide +kernel

theorem six_rep_283 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100200800))) = true := by
  decide +kernel

theorem six_rep_286 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100400000))) = true := by
  decide +kernel

theorem six_rep_289 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100800000))) = true := by
  decide +kernel

theorem six_rep_290 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100820000))) = true := by
  decide +kernel

theorem six_rep_457 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200000200))) = true := by
  decide +kernel

theorem six_rep_458 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200000800))) = true := by
  decide +kernel

theorem six_rep_459 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200000a00))) = true := by
  decide +kernel

theorem six_rep_461 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200008000))) = true := by
  decide +kernel

theorem six_rep_464 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200020000))) = true := by
  decide +kernel

theorem six_rep_470 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200100400))) = true := by
  decide +kernel

theorem six_rep_478 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200410000))) = true := by
  decide +kernel

theorem six_rep_481 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200800000))) = true := by
  decide +kernel

theorem six_rep_482 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x200820000))) = true := by
  decide +kernel

end CDCert.K6
