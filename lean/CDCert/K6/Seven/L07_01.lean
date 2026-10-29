/-
CDCert.K6.Seven.L07_01 — GENERATED kernel checks (Claude's generator `mkseven2.py`) of the
seven-level seed families: family 7: the seven-level inequality at the listed final states, chunks 20..22.
Each theorem is evaluated by the kernel (`decide +kernel`); see `CDCert.K6.Defs7`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).
-/
import CDCert.K6.Table5
import CDCert.K6.Seven.Data
import CDCert.K6.Seven.Fin07
namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

theorem seven_leaf_7_20 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) [fin7_400, fin7_401, fin7_402, fin7_403, fin7_404, fin7_405, fin7_406, fin7_407, fin7_408, fin7_409, fin7_410, fin7_411, fin7_412, fin7_413, fin7_414, fin7_415, fin7_416, fin7_417, fin7_418, fin7_419] = true := by
  decide +kernel

theorem seven_leaf_7_21 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) [fin7_420, fin7_421, fin7_422, fin7_423, fin7_424, fin7_425, fin7_426, fin7_427, fin7_428, fin7_429, fin7_430, fin7_431, fin7_432, fin7_433, fin7_434, fin7_435, fin7_436, fin7_437, fin7_438, fin7_439] = true := by
  decide +kernel

theorem seven_leaf_7_22 : allNat (fun s => leaf7 table5 hintS psiT sKeyT bots7 tops7 14400 (nat_lit 0x30400130000000034cf000000000000000000000000000000000000000000c3300d000000000341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (encS (expand3 s))) [fin7_440] = true := by
  decide +kernel

end CDCert.K6
