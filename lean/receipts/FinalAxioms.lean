-- Receipt: statements and axioms of the final results (compile with `lake env lean receipts/FinalAxioms.lean`).
import CDCert.Main
import CDCert.TwoInputs

-- The definitions the statements depend on (Codex's semantic definitions).
#print Condorcet.IsStrictTotal
#print Condorcet.Order
#print Condorcet.Domain
#print Condorcet.majority
#print Condorcet.IsCondorcet
#print Condorcet.Never
#print Condorcet.ExtremeRestricted
#print Condorcet.IsPeakPit
#print Condorcet.f
#print Condorcet.h

-- Theorem thm:main
#check @CDCert.Main.general_recurrence
#print axioms CDCert.Main.general_recurrence
#check @CDCert.Main.general_geometric
#print axioms CDCert.Main.general_geometric
#check @CDCert.Main.peak_recurrence
#print axioms CDCert.Main.peak_recurrence
#check @CDCert.Main.peak_geometric
#print axioms CDCert.Main.peak_geometric
#check @CDCert.Main.general_limit
#print axioms CDCert.Main.general_limit
#check @CDCert.Main.peak_limit
#print axioms CDCert.Main.peak_limit
#check @CDCert.Main.general_polynomial_correction
#print axioms CDCert.Main.general_polynomial_correction

-- The two inputs (eq:twoinputs) and the transfer (eq:transfer), stated literally
#check @CDCert.TwoInputs.first_input
#print axioms CDCert.TwoInputs.first_input
#check @CDCert.TwoInputs.second_input
#print axioms CDCert.TwoInputs.second_input
#check @CDCert.TwoInputs.transfer
#print axioms CDCert.TwoInputs.transfer

-- Ingredients
#check @CDCert.Recurrences.gap_inequality
#print axioms CDCert.Recurrences.gap_inequality
#check @CDCert.Recurrences.deletion_lower_bound
#print axioms CDCert.Recurrences.deletion_lower_bound
#check @CDCert.Bridge.InF.density
#print axioms CDCert.Bridge.InF.density
#check @CDCert.FreeLocked.free_le_locked
#print axioms CDCert.FreeLocked.free_le_locked
#check @CDCert.K6.finite_lemma
#print axioms CDCert.K6.finite_lemma
#check @CDCert.K6.adj_le
#print axioms CDCert.K6.adj_le
#check @CDCert.Supermult.f_supermul
#print axioms CDCert.Supermult.f_supermul
#check @CDCert.Supermult.h_supermul
#print axioms CDCert.Supermult.h_supermul
-- Stronger forms (all n)
#check @CDCert.Recurrences.general_recurrence
#print axioms CDCert.Recurrences.general_recurrence
#check @CDCert.Bounds.peakPit_recurrence
#print axioms CDCert.Bounds.peakPit_recurrence
