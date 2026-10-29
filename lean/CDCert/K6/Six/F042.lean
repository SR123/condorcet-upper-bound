/-
CDCert.K6.Six.F042 — GENERATED kernel checks (Claude's generator `mkrep6.py`) of the
six-level finite inequality for five-type representatives 637, 774, 784, 818, 992, 1005, 1103, 1107, 1143.
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

theorem six_rep_637 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x3d70410d7))) = true := by
  decide +kernel

theorem six_rep_774 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x101302d08306d))) = true := by
  decide +kernel

theorem six_rep_784 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x108302d01306d))) = true := by
  decide +kernel

theorem six_rep_818 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x301300f0130cf))) = true := by
  decide +kernel

theorem six_rep_992 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xc08302c00f32c))) = true := by
  decide +kernel

theorem six_rep_1005 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0xd01302d00036d))) = true := by
  decide +kernel

theorem six_rep_1103 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10004c00004d7041017))) = true := by
  decide +kernel

theorem six_rep_1107 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x10400130000170014d7))) = true := by
  decide +kernel

theorem six_rep_1143 :
    dfs1 (leafOK6 table5 exc6) groups6 (enc (liftOf lifts6 (nat_lit 0x31004c00004cf00300f))) = true := by
  decide +kernel

end CDCert.K6
