import C72T6.Solutions
import C72T6.Tests
import C72T6.Refute

/-!
# Axiom report for the T6 theorems (order-2 part)

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- Gauge forms, Lemma 3.5 (a) for forms, Lemma 6.1 (b), the bad-syndrome condition (C72T6/Gauge.lean)
#print axioms C72.T6.DT_apply
#print axioms C72.T6.G0_induction
#print axioms C72.T6.G0_symm
#print axioms C72.T6.G0_diag
#print axioms C72.T6.InA0_add
#print axioms C72.T6.G0_apply_disjoint
#print axioms C72.T6.badAt_add_iff
#print axioms C72.T6.ruledOut_add_iff
#print axioms C72.T6.H_D_iff

-- The slice property and the bridge to H_D (C72T6/Slice.lean)
#print axioms C72.T6.EchelonBasis.φ_sum
#print axioms C72.T6.slice_existsUnique
#print axioms C72.T6.sliceRep_mem_slice
#print axioms C72.T6.sliceRep_sub_mem
#print axioms C72.T6.forall_of_slice
#print axioms C72.T6.H_D_of_slice
#print axioms C72.T6.slice_A0_existsUnique
#print axioms C72.T6.exists_echelonBasis
#print axioms C72.T6.exists_echelonBasis_of_finite
#print axioms C72.T6.exists_echelonBasis_G0

-- Lemma 6.3, the action of Aut(Y) on forms, keys and the tests (C72T6/Search.lean)
#print axioms C72.T6.lemma63_abstract
#print axioms C72.T6.autLin_coe
#print axioms C72.T6.autLin_mul
#print axioms C72.T6.autLin_inv_apply
#print axioms C72.T6.formAct_apply
#print axioms C72.T6.formAct_mul
#print axioms C72.T6.autLin_allOnes
#print axioms C72.T6.InA0_formAct
#print axioms C72.T6.formAct_add
#print axioms C72.T6.formAct_DT
#print axioms C72.T6.formAct_mem_G0
#print axioms C72.T6.indicator_map
#print axioms C72.T6.ruledOut_of_ruledOut_formAct
#print axioms C72.T6.lemma63_order2
#print axioms C72.T6.syn_add
#print axioms C72.T6.syn_formAct
#print axioms C72.T6.key_lt_of_head_lt
#print axioms C72.T6.lt_of_leading_bits_lt
#print axioms C72.T6.key_lt_of_first_diff
#print axioms C72.T6.key_add
#print axioms C72.T6.lemma63_key
#print axioms C72.T6.first_test
#print axioms C72.T6.coset_rule
#print axioms C72.T6.second_test

-- Converse directions of Lemmas 3.3 and 3.6, Proposition 6.2 backward (C72T6/Converse.lean)
#print axioms C72.T6.pv_self_mem_CB
#print axioms C72.T6.exists_mem_CB
#print axioms C72.T6.CB_selfDual
#print axioms C72.T6.CB_doublyEven
#print axioms C72.T6.aStd_mem_CB
#print axioms C72.T6.Yof_CB
#print axioms C72.T6.minWt_CB
#print axioms C72.T6.prop62_converse

-- The paper's bad sets, Lemma 3.6 in both directions, Proposition 6.2 (C72T6/Solutions.lean)
#print axioms C72.T6.two_mul_lt_of_mem_Eset
#print axioms C72.T6.mem_Eset_of
#print axioms C72.T6.badAt_of_badAtE
#print axioms C72.T6.badAtE_of_badAt
#print axioms C72.T6.ruledOut_iff_ruledOutE
#print axioms C72.T6.lemma36_iff
#print axioms C72.T6.isSol_iff_isSolE
#print axioms C72.T6.H_D_iff_E
#print axioms C72.T6.prop62_forward
#print axioms C72.T6.prop62_forward_slice
#print axioms C72.T6.prop62_converse_E

-- The toy code Y4 (C72T6/Toy.lean)
#print axioms C72.T6.Toy.mem_Y4
#print axioms C72.T6.Toy.dot_four
#print axioms C72.T6.Toy.Y4_selfDual
#print axioms C72.T6.Toy.allOnes_mem_Y4
#print axioms C72.T6.Toy.Y4_eq
#print axioms C72.T6.Toy.B4_InA0

-- Tests (C72T6/Tests.lean)
#print axioms C72.T6.Tests.test_converse_Y4
#print axioms C72.T6.Tests.test_disjoint_Y4
#print axioms C72.T6.Tests.test_echelon_Yc
#print axioms C72.T6.Tests.test_key_head
#print axioms C72.T6.Tests.test_key_first_diff
#print axioms C72.T6.Tests.test_leading_bits

-- Refutations behind the controls (C72T6/Refute.lean)
#print axioms C72.T6.Refute.DT_overlap
#print axioms C72.T6.Refute.lemma61b_needs_disjoint
#print axioms C72.T6.Refute.ψ2_apply
#print axioms C72.T6.Refute.slice_needs_pivot
#print axioms C72.T6.Refute.lemma63_needs_strict
#print axioms C72.T6.Refute.bits_need_leading
#print axioms C72.T6.Refute.CB_doublyEven_needs_diag
#print axioms C72.T6.Refute.CB_selfDual_needs_symm
