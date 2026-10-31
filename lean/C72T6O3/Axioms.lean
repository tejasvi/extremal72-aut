import C72T6O3.Perm24
import C72T6O3.M24Data
import C72T6O3.Closure
import C72T6O3.M24
import C72T6O3.Lemma44
import C72T6O3.Lemma44General
import C72T6O3.Orders
import C72T6O3.Prop43
import C72T6O3.Tests

/-!
# Axiom report for the T6 (order 3) theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- Permutations from codes
#print axioms C72.Three.M24.invPair_spec
#print axioms C72.Three.M24.mem_Aut_of_autOK

-- Octads and the closure certificate
#print axioms C72.Three.M24.wt_add_binary
#print axioms C72.Three.M24.eq_of_five
#print axioms C72.Three.M24.isOctad_map
#print axioms C72.Three.M24.map_octad_eq
#print axioms C72.Three.M24.closeIter_F0
#print axioms C72.Three.M24.closeIter_sound
#print axioms C72.Three.M24.eq_one_of_fixes

-- The M24 facts
#print axioms C72.Three.M24.O0_eq
#print axioms C72.Three.M24.O0_isOctad
#print axioms C72.Three.M24.pp_spec
#print axioms C72.Three.M24.q1_spec
#print axioms C72.Three.M24.transOK_eq
#print axioms C72.Three.M24.trans_spec
#print axioms C72.Three.M24.five_transitive
#print axioms C72.Three.M24.rho_spec
#print axioms C72.Three.M24.kqOK_eq
#print axioms C72.Three.M24.kq_spec
#print axioms C72.Three.M24.map_O0_of_InH
#print axioms C72.Three.M24.InK_of_InH
#print axioms C72.Three.M24.InH_eq_rho_pow_mul
#print axioms C72.Three.M24.InK_eq_one

-- Orders
#print axioms C72.Three.M24.card_K
#print axioms C72.Three.M24.card_H
#print axioms C72.Three.M24.card_Aut_G24

-- Lemma 4.4
#print axioms C72.Three.M24.map_permute_eq_iff
#print axioms C72.Three.M24.map_O0_mul_InK
#print axioms C72.Three.M24.map_O0_mul_InH
#print axioms C72.Three.M24.lemma44_exists
#print axioms C72.Three.M24.lemma44_unique
#print axioms C72.Three.M24.lemma44
#print axioms C72.Three.M24.octad_eq_of_five
#print axioms C72.Three.M24.normalFormAt_base
#print axioms C72.Three.M24.normalFormAt_iff
#print axioms C72.Three.M24.exists_transport
#print axioms C72.Three.M24.lemma44_general
#print axioms C72.Three.M24.isDodecad_map
#print axioms C72.Three.M24.validGolay_mul_iff
#print axioms C72.Three.M24.exists_validGolay_iff_normalForm

-- Proposition 4.3, converse direction and class invariance
#print axioms C72.Three.W_of_validGolay
#print axioms C72.Three.eq_zero_of_tr_wb
#print axioms C72.Three.prop43_converse
#print axioms C72.Three.prop43
#print axioms C72.Three.SuppEquiv.symm
#print axioms C72.Three.SuppEquiv.trans
#print axioms C72.Three.validGolay_of_suppEquiv
#print axioms C72.Three.supp_monomial
#print axioms C72.Three.suppEquiv_monomial
#print axioms C72.Three.suppEquiv_conj
#print axioms C72.Three.suppEquiv_of_monConjEquiv
#print axioms C72.Three.exists_validGolay_iff

-- Tests
#print axioms C72.Three.M24.Tests.normalForm_one
#print axioms C72.Three.M24.Tests.unique_normal_G24
#print axioms C72.Three.M24.Tests.not_normalForm_rho
#print axioms C72.Three.M24.Tests.not_normalForm_kq6
#print axioms C72.Three.M24.Tests.kq6_ne_one
#print axioms C72.Three.M24.Tests.swap_not_mem_Aut
#print axioms C72.Three.M24.Tests.closeIter_without_q1
