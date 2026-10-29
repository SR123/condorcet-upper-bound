/-
CDCert.K6.Seven.FamB — GENERATED kernel checks (Claude's generator `mkfamb.py`): the re-ordered seed
families `fam7b_3`, `fam7b_4`, `fam7b_5` are the groups of `groupsD7` in the orders `ord7b_i`
(permutations of the 56 groups), restricted to the options containing the seed (`seedOK`), as in
`CDCert.K6.Seven.Fam`.

Part of the Lean formalisation of the Moros–Riis upper bounds for Condorcet
domains (deletion/gap framework originated by Pavlos Moros; improved bounds and
further mathematical improvements led by Søren Riis).

Lean 4.26.0, core only. No `sorry`, no custom axioms, no `native_decide`.
-/
import CDCert.K6.Seven.Fam
import CDCert.K6.Seven.FamBDef

namespace CDCert.K6

set_option maxRecDepth 100000
set_option Elab.async false

def ord7b_3 : List Nat := [41, 15, 42, 46, 16, 19, 25, 43, 47, 50, 51, 35, 36, 0, 38, 2, 6, 37, 9, 5, 1, 20, 44, 26, 48, 17, 31, 53, 28, 22, 39, 10, 3, 7, 12, 34, 24, 30, 18, 8, 4, 11, 29, 23, 40, 45, 49, 54, 55, 52, 13, 14, 27, 21, 32, 33]
theorem ord7b_3_perm : (ord7b_3).Perm (List.range 56) := by decide
theorem fam7b_3_eq : fam7b_3 = (ord7b_3).map (fun g => (ocG3.getD g []).filter (seedOK (nat_lit 0x34cf000000000000000000000000000000000000000000000000000000000141000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) := by
  decide +kernel

def ord7b_4 : List Nat := [35, 0, 36, 41, 1, 5, 15, 37, 42, 46, 25, 47, 50, 6, 9, 38, 16, 19, 43, 2, 39, 53, 12, 13, 40, 54, 55, 14, 34, 48, 7, 51, 10, 26, 28, 31, 49, 8, 29, 30, 17, 22, 23, 44, 20, 33, 32, 45, 52, 3, 27, 24, 11, 4, 18, 21]
theorem ord7b_4_perm : (ord7b_4).Perm (List.range 56) := by decide
theorem fam7b_4_eq : fam7b_4 = (ord7b_4).map (fun g => (ocG1.getD g []).filter (seedOK (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) := by
  decide +kernel

def ord7b_5 : List Nat := [35, 0, 36, 41, 1, 5, 15, 37, 42, 46, 25, 47, 50, 6, 9, 38, 16, 19, 43, 2, 39, 53, 12, 13, 40, 54, 45, 23, 4, 22, 44, 3, 48, 7, 28, 17, 51, 10, 20, 26, 31, 34, 30, 33, 27, 29, 32, 49, 52, 55, 8, 18, 11, 21, 14, 24]
theorem ord7b_5_perm : (ord7b_5).Perm (List.range 56) := by decide
theorem fam7b_5_eq : fam7b_5 = (ord7b_5).map (fun g => (ocG3.getD g []).filter (seedOK (nat_lit 0x30cf0030cf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) := by
  decide +kernel

end CDCert.K6
