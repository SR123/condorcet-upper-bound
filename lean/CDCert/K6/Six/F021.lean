/-
CDCert.K6.Six.F021 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 404, 410, 444, 447, 449, 455, 569, 626, 705, 716, 721, 765, 773, 778, 839, 852, 1025, 1082.
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

theorem six_rep_404 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1c71014c7))) = true := by
  decide +kernel

theorem six_rep_410 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1cf000ccf))) = true := by
  decide +kernel

theorem six_rep_444 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1d7141017))) = true := by
  decide +kernel

theorem six_rep_447 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f30003f3))) = true := by
  decide +kernel

theorem six_rep_449 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f3000cf3))) = true := by
  decide +kernel

theorem six_rep_455 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x1f35c0033))) = true := by
  decide +kernel

theorem six_rep_569 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x34d03300d))) = true := by
  decide +kernel

theorem six_rep_626 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d30401d3))) = true := by
  decide +kernel

theorem six_rep_705 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x14c71004c7))) = true := by
  decide +kernel

theorem six_rep_716 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x20ba0024ba))) = true := by
  decide +kernel

theorem six_rep_721 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x30cf0030cf))) = true := by
  decide +kernel

theorem six_rep_765 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x100302d48006d))) = true := by
  decide +kernel

theorem six_rep_773 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101302d08006d))) = true := by
  decide +kernel

theorem six_rep_778 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108002d01306d))) = true := by
  decide +kernel

theorem six_rep_839 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x400302c08712c))) = true := by
  decide +kernel

theorem six_rep_852 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x408302c00712c))) = true := by
  decide +kernel

theorem six_rep_1025 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x170010070005c7))) = true := by
  decide +kernel

theorem six_rep_1082 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x2008080020cb8220))) = true := by
  decide +kernel

end CDCert.K6
