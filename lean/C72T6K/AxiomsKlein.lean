import C72T6K.Prop37
import C72T6K.KleinTests
import C72T6K.KleinRefute

/-!
# Axiom report for the T6 theorems of the Klein case (Lemma 3.4, Lemma 3.5 (b), (c) for forms, Proposition 3.7)

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- The second involution (Lemma 3.4), the space G, orbit representatives, conjugation (C72T6K/Klein.lean)
#print axioms C72.T6.liftP_apply
#print axioms C72.T6.permute_liftP_pv
#print axioms C72.T6.liftP_mul_aStd
#print axioms C72.T6.liftP_mul
#print axioms C72.T6.aStd_apply'
#print axioms C72.T6.pv_self_apply
#print axioms C72.T6.swapP_apply
#print axioms C72.T6.swapP_mul_self
#print axioms C72.T6.swapP_mul_aStd
#print axioms C72.T6.permute_swapP_pv_self
#print axioms C72.T6.pair_form
#print axioms C72.T6.pair_form_props
#print axioms C72.T6.pair_form_fpf
#print axioms C72.T6.permute_pv_self_of_pair_form
#print axioms C72.T6.mem_Aut_Yof_of_pair_form
#print axioms C72.T6.exists_swapP
#print axioms C72.T6.swapP_conj
#print axioms C72.T6.liftP_mem_Aut_CB_iff
#print axioms C72.T6.GK_le_G0
#print axioms C72.T6.exists_echelonBasis_GK
#print axioms C72.T6.formAct_DT_of_invariant
#print axioms C72.T6.formAct_DT_of_transversal
#print axioms C72.T6.formAct_of_mem_GK
#print axioms C72.T6.InA_add
#print axioms C72.T6.badAt_formAct
#print axioms C72.T6.badAt_iff_of_invariant
#print axioms C72.T6.ruledOut_iff_reps
#print axioms C72.T6.isFPFInv_conj
#print axioms C72.T6.InA_conj

-- Proposition 3.7 (C72T6K/Prop37.lean)
#print axioms C72.T6.kleinPair_of_mulEquiv
#print axioms C72.T6.aStd_mul_self
#print axioms C72.T6.permute_permCongr_reindex
#print axioms C72.T6.not_ruledOut_of_minWt
#print axioms C72.T6.klein_forward_pairs
#print axioms C72.T6.exists_isSolK
#print axioms C72.T6.ruledOut_iff_reps_E
#print axioms C72.T6.isSolK_iff_isSolKE
#print axioms C72.T6.prop37_forward
#print axioms C72.T6.prop37_forward_slice
#print axioms C72.T6.prop37_forward_reps
#print axioms C72.T6.kleinPair_CB
#print axioms C72.T6.prop37_converse
#print axioms C72.T6.prop38_of_searches

-- Tests on the toy code (C72T6K/KleinTests.lean)
#print axioms C72.T6.KleinTests.β4_symm_0
#print axioms C72.T6.KleinTests.β4_symm_1
#print axioms C72.T6.KleinTests.β4_symm_2
#print axioms C72.T6.KleinTests.β4_symm_3
#print axioms C72.T6.KleinTests.β4_mem_Aut
#print axioms C72.T6.KleinTests.test_isFPFInv_β4
#print axioms C72.T6.KleinTests.B4_invariant
#print axioms C72.T6.KleinTests.test_InA_toy
#print axioms C72.T6.KleinTests.test_kleinPair_toy
#print axioms C72.T6.KleinTests.test_DT_transversal
#print axioms C72.T6.KleinTests.test_DT_invariant

-- Refutations behind the controls (C72T6K/KleinRefute.lean)
#print axioms C72.T6.KleinRefute.bK_apply_00
#print axioms C72.T6.KleinRefute.bK_apply_01
#print axioms C72.T6.KleinRefute.pair_form_needs_commute
#print axioms C72.T6.KleinRefute.liftP_needs_invariance
#print axioms C72.T6.KleinRefute.transversal_needs_selfDual
