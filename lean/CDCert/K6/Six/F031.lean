/-
CDCert.K6.Six.F031 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 572, 579, 585, 595, 598, 646, 663, 905, 1020, 1093, 1131, 1151, 1159.
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

theorem six_rep_572 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d41700d))) = true := by
  decide +kernel

theorem six_rep_579 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d03302d))) = true := by
  decide +kernel

theorem six_rep_585 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x36d48006d))) = true := by
  decide +kernel

theorem six_rep_595 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c302c3c3))) = true := by
  decide +kernel

theorem six_rep_598 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3c31045c3))) = true := by
  decide +kernel

theorem six_rep_646 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3f3cc0033))) = true := by
  decide +kernel

theorem six_rep_663 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x5cf0030cf))) = true := by
  decide +kernel

theorem six_rep_905 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x70410170001d7))) = true := by
  decide +kernel

theorem six_rep_1020 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xf0400170003d7))) = true := by
  decide +kernel

theorem six_rep_1093 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10000130000170014d7))) = true := by
  decide +kernel

theorem six_rep_1131 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20400100000381c2438))) = true := by
  decide +kernel

theorem six_rep_1151 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100400100000305d0430))) = true := by
  decide +kernel

theorem six_rep_1159 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10040000041c00001d3040013))) = true := by
  decide +kernel

end CDCert.K6
