import C72T4.Main
import C72T4.Refute
import C72T4.Tests

/-!
# Axiom report for the T4 theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- Relabelling of codes
#print axioms C72.T4.wt_reindex
#print axioms C72.T4.dotProduct_reindex
#print axioms C72.T4.dual_map_reindex
#print axioms C72.T4.SelfDual.map_reindex
#print axioms C72.T4.TypeII.map_reindex
#print axioms C72.T4.MinWt.map_reindex
#print axioms C72.T4.MinWtEq.map_reindex
#print axioms C72.T4.map_reindex_trans

-- The pair model (Section 3.1) and duality
#print axioms C72.T4.dual_dual
#print axioms C72.T4.dual_sup
#print axioms C72.T4.allOnes_mem_of_selfDual
#print axioms C72.T4.permute_aStd_pv
#print axioms C72.T4.wt_pv
#print axioms C72.T4.dotProduct_pv
#print axioms C72.T4.wt_pv_add

-- Lemma 3.2 with Lemma 3.3 (b), (c) forward
#print axioms C72.T4.Yof_le_map_sigmaL
#print axioms C72.T4.model

-- Lemma 3.6 (the direction used)
#print axioms C72.T4.exists_dotProduct_eq
#print axioms C72.T4.mem_dual_suppOn
#print axioms C72.T4.lemma36

-- The 41 codes
#print axioms C72.T4.orthoCheck_all
#print axioms C72.T4.pivotCheck_all
#print axioms C72.T4.row_dotProduct_row
#print axioms C72.T4.row_linearIndependent
#print axioms C72.T4.finrank_Yc
#print axioms C72.T4.Yc_selfDual
#print axioms C72.T4.allOnes_mem_Yc

-- Relabelling a fixed-point-free involution to the pair model
#print axioms C72.T4.sameCycle_involution
#print axioms C72.T4.pairEquiv_apply_apply
#print axioms C72.T4.permute_aStd_reindex
#print axioms C72.T4.Yof_map_pairEquiv
#print axioms C72.T4.two_mul_card_orbits
#print axioms C72.T4.card_orbits

-- Theorem D and "no involution"
#print axioms C72.T4.thmD_of_HD
#print axioms C72.T4.noFPFInv_of
#print axioms C72.T4.noInv_of_T4
#print axioms C72.T4.main_of_T4

-- Refutation and tests
#print axioms C72.T4.Refute.model_needs_selfDual
#print axioms C72.T4.Refute.orthogonal_of_selfDual_Yof_RM
#print axioms C72.T4.Tests.aStd_swaps_halves
#print axioms C72.T4.Tests.wt_pv_add_example
#print axioms C72.T4.Tests.CB_rep2_example
#print axioms C72.T4.Tests.wt_row_0_0
#print axioms C72.T4.Tests.card_orbits_stdPerm
