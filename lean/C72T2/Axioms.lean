import C72T2.Basic
import C72T2.F4
import C72T2.Hermitian
import C72T2.Coords
import C72T2.Golay
import C72T2.Reduction
import C72T2.Lemma42
import C72T2.TheoremB
import C72T2.Tests
import C72T2.OctDod
import C72T2.HCBProgram
import C72T2.G24F4

/-!
# Axiom report for the T2 theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- The field 𝔽₄ and ψ
#print axioms C72.F4.instCommRing
#print axioms C72.F4.instField
#print axioms C72.F4.w_sq
#print axioms C72.F4.star_eq_sq
#print axioms C72.F4.mul_star_self
#print axioms C72.F4.tr_spec
#print axioms C72.F4.tr_sum
#print axioms C72.F4.eq_zero_of_tr
#print axioms C72.F4.psi_add
#print axioms C72.F4.psi_injective
#print axioms C72.F4.psi_w_mul
#print axioms C72.F4.psi_sum
#print axioms C72.F4.cycle_wt_psi
#print axioms C72.F4.psi_dot
#print axioms C72.F4.psi_dotProduct
#print axioms C72.F4.tr_mul_star
#print axioms C72.F4.psi_psiInv
#print axioms C72.F4.psi_cycle_sum
#print axioms C72.F4.cycle_weight
#print axioms C72.F4.natCast_eq

-- Hermitian duality
#print axioms C72.F4.hform_add_right
#print axioms C72.F4.hform_smul_right
#print axioms C72.F4.mem_hdual_span
#print axioms C72.F4.hform_self
#print axioms C72.F4.even_wt_of_le_hdual
#print axioms C72.F4.HSelfDual.even_wt

-- Coordinates, σ, g ↦ g^(3), φ, Lemma 4.1
#print axioms C72.Three.sum_fin72
#print axioms C72.Three.sigma3_idx
#print axioms C72.Three.sigma3_symm_idx
#print axioms C72.Three.orderOf_sigma3
#print axioms C72.Three.sigma3_apply_ne
#print axioms C72.Three.e0_sigma3_idx'
#print axioms C72.Three.e0_sigma3_idx
#print axioms C72.Three.permute_sigma3_phi
#print axioms C72.Three.permute_sigma3_triple
#print axioms C72.Three.wt_triple
#print axioms C72.Three.wt_phi
#print axioms C72.Three.dotProduct_triple
#print axioms C72.Three.dotProduct_triple_phi
#print axioms C72.Three.dotProduct_phi
#print axioms C72.Three.lemma41

-- G24
#print axioms C72.Three.toVec_xor
#print axioms C72.Three.g24gen_spec
#print axioms C72.Three.chk_sound
#print axioms C72.Three.g24_chk
#print axioms C72.Three.g24_okWt
#print axioms C72.Three.G24_wt
#print axioms C72.Three.g24gen_linearIndependent
#print axioms C72.Three.finrank_G24
#print axioms C72.Three.g24gen_orth
#print axioms C72.Three.G24_selfDual
#print axioms C72.Three.G24_typeII
#print axioms C72.Three.G24_minWt
#print axioms C72.Three.G24_wt8

-- The codes G and E, the decomposition
#print axioms C72.Three.mem_Ecode_iff
#print axioms C72.Three.fixed_eq_triple
#print axioms C72.Three.even_eq_phi
#print axioms C72.Three.mem_Fsub_iff_triple
#print axioms C72.Three.mem_Esub_iff_phi
#print axioms C72.Three.exists_triple_add_phi
#print axioms C72.Three.Cof_Gcode_Ecode
#print axioms C72.Three.Gcode_selfDual
#print axioms C72.Three.Ecode_hselfDual
#print axioms C72.Three.Gcode_typeII
#print axioms C72.Three.Gcode_minWt
#print axioms C72.Three.Ecode_minWt

-- Lemma 4.2
#print axioms C72.Three.lemma42_forward
#print axioms C72.Three.lemma42_converse
#print axioms C72.Three.lemma42

-- Proposition 4.3 (forward) and Theorem B
#print axioms C72.Three.supp_permute
#print axioms C72.H_CB_iff
#print axioms C72.prop43_forward
#print axioms C72.thmB_of
#print axioms C72.main_of_cited_thmB

-- Tests and refutations
#print axioms C72.Three.Tests.psi_values
#print axioms C72.Three.Tests.w_order
#print axioms C72.Three.Tests.refute_trace_bilinear
#print axioms C72.Three.Tests.sigma3_values
#print axioms C72.Three.Tests.sigma3_phi_example
#print axioms C72.Three.Tests.refute_action_wb
#print axioms C72.Three.Tests.lemma41_example
#print axioms C72.Three.Tests.not_minWt_G24_12
#print axioms C72.Three.Tests.tau23_values
#print axioms C72.Three.Tests.tau23_mem_Aut
#print axioms C72.Three.Tests.G24_check
#print axioms C72.Three.Tests.E2_hselfDual
#print axioms C72.Three.Tests.E2_not_bilinear

-- The octads and dodecads of G24 are those of octdod.txt
#print axioms C72.Three.mem_words
#print axioms C72.Three.words_complete
#print axioms C72.Three.echelon_orth
#print axioms C72.Three.g24mask_mem_words
#print axioms C72.Three.words_filter_octads
#print axioms C72.Three.words_filter_dodecads
#print axioms C72.Three.octMasks_length
#print axioms C72.Three.dodMasks_length
#print axioms C72.Three.octMasks_nodup
#print axioms C72.Three.dodMasks_nodup
#print axioms C72.Three.span_echelon
#print axioms C72.Three.mem_G24_iff_words
#print axioms C72.Three.isOctad_iff
#print axioms C72.Three.isDodecad_iff
#print axioms C72.Three.mem_G24_of_orth
#print axioms C72.H_CB_iff_octdod

-- G24 ⊗ F4: the antecedents of H_LP and H_CB are satisfiable
#print axioms C72.Three.G24F4_eq
#print axioms C72.Three.mem_G24F4_iff
#print axioms C72.Three.supp_incl_add
#print axioms C72.Three.incl_gen_orth
#print axioms C72.Three.hform_incl
#print axioms C72.Three.G24F4_le_hdual
#print axioms C72.Three.hdual_G24F4_le
#print axioms C72.Three.G24F4_minWt
#print axioms C72.Three.G24F4_wt8
#print axioms C72.Three.G24F4_antecedent
