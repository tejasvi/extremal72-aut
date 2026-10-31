import C72T3.Tests

/-!
# Axiom report for the T3 theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- The field 𝔽₁₆, ψ, the trace and the norm classes
#print axioms C72.T3.F16.instField
#print axioms C72.T3.F16.t_minpoly
#print axioms C72.T3.F16.eq_poly
#print axioms C72.T3.F16.orderOf_t
#print axioms C72.T3.F16.star_star
#print axioms C72.T3.F16.star_t
#print axioms C72.T3.psi_injective
#print axioms C72.T3.psi_psiInv
#print axioms C72.T3.psi_t_mul
#print axioms C72.T3.dot_psi
#print axioms C72.T3.tr_nondeg
#print axioms C72.T3.cls_eq_one
#print axioms C72.T3.cls_reps
#print axioms C72.T3.norms_F4
#print axioms C72.T3.wpsi_cls
#print axioms C72.T3.norm_cls
#print axioms C72.T3.wpsi_lam

-- The words of e8 and M
#print axioms C72.T3.card_e8Words
#print axioms C72.T3.sideTerm_eq
#print axioms C72.T3.M_zero
#print axioms C72.T3.wordVec_mem_e8
#print axioms C72.T3.wordVec_injective
#print axioms C72.T3.sideWt_wordVec

-- Coordinates, φ₀ and φ₁
#print axioms C72.T3.E72_val
#print axioms C72.T3.orderOf_g5
#print axioms C72.T3.exists_phi0_eq
#print axioms C72.T3.phi0_dot
#print axioms C72.T3.phi0_injective
#print axioms C72.T3.permute_g5_phi1
#print axioms C72.T3.phi1_injective
#print axioms C72.T3.phi1_dot
#print axioms C72.T3.phi1_dot_phi0
#print axioms C72.T3.wt_phi0_add_phi1
#print axioms C72.T3.eq_zero_of_phi0_add_phi1

-- Decomposition, C₀ and C₁
#print axioms C72.T3.Fsub_eq_map_C0
#print axioms C72.T3.selfDual_C0
#print axioms C72.T3.exists_phi1_of_mem_Esub
#print axioms C72.T3.smul_mem_C1
#print axioms C72.T3.herm_eq_zero
#print axioms C72.T3.C1_hSelfDual
#print axioms C72.T3.finrank_Esub
#print axioms C72.T3.card_C1_ge

-- e8 ⊕ e8 and d₁₆⁺
#print axioms C72.T3.e8e8_typeII
#print axioms C72.T3.d16plus_typeII
#print axioms C72.T3.e8e8_pair
#print axioms C72.T3.d16plus_pair
#print axioms C72.T3.tauP_mem_Aut
#print axioms C72.T3.sumPerm_mem_Aut
#print axioms C72.T3.mem_e8e8w

-- Lemma 2.1
#print axioms C72.T3.wt_phi0
#print axioms C72.T3.C0_typeII
#print axioms C72.T3.C0_minWt
#print axioms C72.T3.C0_no_w4_both
#print axioms C72.T3.not_permEquiv_d16plus
#print axioms C72.T3.lemma21_C0
#print axioms C72.T3.liftP_comm
#print axioms C72.T3.lemma21

-- Lemma 2.2
#print axioms C72.T3.wt_sides
#print axioms C72.T3.lemma22

-- Lemma 2.3
#print axioms C72.T3.L23.chk16_0
#print axioms C72.T3.L23.chk16_1
#print axioms C72.T3.L23.chk16_2
#print axioms C72.T3.L23.chk16_3
#print axioms C72.T3.L23.chk12_0
#print axioms C72.T3.okPat_all
#print axioms C72.T3.sideTerm_word
#print axioms C72.T3.xor_cls_eq_zero
#print axioms C72.T3.lemma23

-- The reduction to U and Theorem A
#print axioms C72.T3.eq_zero_of_cB_eq_zero
#print axioms C72.T3.eq_zero_of_cA_eq_zero
#print axioms C72.T3.core
#print axioms C72.H_A_iff
#print axioms C72.thmA_of_hyps

-- Tests
#print axioms C72.T3.Tests.M_single
#print axioms C72.T3.Tests.two_le_M
#print axioms C72.T3.Tests.one_unitary
#print axioms C72.T3.Tests.not_H_Athr_four
#print axioms C72.T3.Tests.M_single_add
#print axioms C72.T3.Tests.e8e8_not_equiv_d16plus
#print axioms C72.T3.Tests.keyRow_mem_R
