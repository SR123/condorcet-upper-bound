import CDCert
open CDCert CDCert.Rows CDCert.Examples
-- Dedup
#print axioms CDCert.mem_dedup
#print axioms CDCert.nodup_dedup
-- Enum
#print axioms CDCert.filter_eq_filter_iff
#print axioms CDCert.domainOf_eq_iff
#print axioms CDCert.mem_allChoices
#print axioms CDCert.IsChoice.map
#print axioms CDCert.IsChoice.of_map
#print axioms CDCert.mem_enumerate
#print axioms CDCert.nodup_enumerate
#print axioms CDCert.mem_enumerate_iff_naive
#print axioms CDCert.mem_enumPruneFrom
#print axioms CDCert.mem_dfs
-- Slice
#print axioms CDCert.isChoice_requireSlice
#print axioms CDCert.mem_enumerate_requireSlice
#print axioms CDCert.exactSliceB_eq_true
#print axioms CDCert.exactSlice_iff
#print axioms CDCert.pruneForbidden_sound
#print axioms CDCert.mem_enumerateExact
#print axioms CDCert.nodup_enumerateExact
#print axioms CDCert.mem_enumerateExactDFS
#print axioms CDCert.mem_enumerateExact_iff_filter
-- Check
#print axioms CDCert.dfsCheck_sound
#print axioms CDCert.dfsCheck_noPrune_iff
#print axioms CDCert.dfsCheck_append_of_forall
#print axioms CDCert.runChoice_sim
#print axioms CDCert.runChoice_filter
-- RowCheck
#print axioms CDCert.Rows.dot?_eq_some_iff
#print axioms CDCert.Rows.rowOK_eq_true
#print axioms CDCert.Rows.checkRows_sound
#print axioms CDCert.Rows.checkRows_iff
#print axioms CDCert.Rows.dotSpec_vsum
#print axioms CDCert.Rows.certified_sum_nonneg
#print axioms CDCert.Rows.certified_inequality_of_cover
-- Examples (decide-based)
#print axioms CDCert.Examples.cert0_rows_nonneg
-- Bitset
#print axioms CDCert.Bits.decode_and_maskOf
#print axioms CDCert.Bits.decode_runChoice_full
#print axioms CDCert.Bits.length_decode
#print axioms CDCert.Bits.pruneB_sound
#print axioms CDCert.Bits.dfsCheckB_sound
#print axioms CDCert.Bits.exactB_iff
#print axioms CDCert.Bits.coverage_of_dfsCheckB
#print axioms CDCert.Bits.coverage_of_dfsCheckB_noPrune
-- Bitset regression (decide +kernel)
#print axioms CDCert.ExamplesBits.pp4_card_le_nine
#print axioms CDCert.ExamplesBits.all4_card_le_nine
#print axioms CDCert.ExamplesBits.pp4_exact_card_le_nine
-- Levels (certificates)
#print axioms CDCert.invariant_sound
#print axioms CDCert.Bits.NTree.mem_sound
#print axioms CDCert.Bits.pruneC_sound
#print axioms CDCert.Bits.certOK_sound
#print axioms CDCert.Bits.coverage_of_certB
-- PermsNodup
#print axioms CDCert.Examples.nodup_perms
#print axioms CDCert.Examples.orders_nodup
