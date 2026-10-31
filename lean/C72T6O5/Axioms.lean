import C72T6O5.Coll
import C72T6O5.Sym
import C72T6O5.Key
import C72T6O5.Scan
import C72T6O5.Normal
import C72T6O5.Table1
import C72T6O5.Tests

/-!
# Axiom report for the T6 (order 5) theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- Collineations
#print axioms C72.T6O5.third_mem
#print axioms C72.T6O5.third_of_mem_line
#print axioms C72.T6O5.card_ncTriples
#print axioms C72.T6O5.triplesOK_eq_true
#print axioms C72.T6O5.linesOK_sound
#print axioms C72.T6O5.injOK_sound
#print axioms C72.T6O5.isColl_collOf
#print axioms C72.T6O5.coe_eq_tableOf
#print axioms C72.T6O5.nc_of_isColl
#print axioms C72.T6O5.isColl_ext
#print axioms C72.T6O5.card_collineations
#print axioms C72.T6O5.isColl_one
#print axioms C72.T6O5.isColl_mul
#print axioms C72.T6O5.isColl_inv
#print axioms C72.T6O5.exists_isColl_apply_eq_zero
#print axioms C72.T6O5.image_mem_e8Words
#print axioms C72.T6O5.sideTerm_comp
#print axioms C72.T6O5.M_comp

-- The symmetries (a)-(c) and the conditions of Proposition 2.4
#print axioms C72.T6O5.H_A_iff_forall_not_sol
#print axioms C72.T6O5.inv_diagonal_mu5
#print axioms C72.T6O5.inv_permMatrix
#print axioms C72.T6O5.scale_apply
#print axioms C72.T6O5.perm_apply
#print axioms C72.T6O5.unitary_of_scale
#print axioms C72.T6O5.unitary_of_perm
#print axioms C72.T6O5.unitary_frob
#print axioms C72.T6O5.cond_of_scale
#print axioms C72.T6O5.cond_of_perm
#print axioms C72.T6O5.cond_frob
#print axioms C72.T6O5.step_sol
#print axioms C72.T6O5.reach_sol

-- Patterns and keys
#print axioms C72.T6O5.key_le
#print axioms C72.T6O5.exists_key_eq
#print axioms C72.T6O5.cls_sq
#print axioms C72.T6O5.cls_eq_of_pattern_eq
#print axioms C72.T6O5.key_congr
#print axioms C72.T6O5.key_comp
#print axioms C72.T6O5.key_frob
#print axioms C72.T6O5.key_img
#print axioms C72.T6O5.key_le_orbit
#print axioms C72.T6O5.exists_orbit_eq_key

-- The scan and the normalisation of a joining entry
#print axioms C72.T6O5.depth_rowAt
#print axioms C72.T6O5.scanIdx_inj
#print axioms C72.T6O5.joins_congr
#print axioms C72.T6O5.iff_of_eqvGen_of_isolated
#print axioms C72.T6O5.normalise_joining
#print axioms C72.T6O5.first_rep
#print axioms C72.T6O5.row0_rep

-- Lemma 2.5
#print axioms C72.T6O5.NFiii_iff_upto
#print axioms C72.T6O5.upto_succ
#print axioms C72.T6O5.exists_NFiii_upto
#print axioms C72.T6O5.lemma25
#print axioms C72.T6O5.lemma25_sol
#print axioms C72.T6O5.H_A_iff_nf
#print axioms C72.T6O5.row0_eq_of_key

-- Table 1
#print axioms C72.T6O5.keyRow_key
#print axioms C72.T6O5.keyRow_key_injective
#print axioms C72.T6O5.row0_eq_keyRow

-- Tests
#print axioms C72.T6O5.Tests.normalForm_one
#print axioms C72.T6O5.Tests.reach_one_diag_t
#print axioms C72.T6O5.Tests.not_NFiii_diag_t
#print axioms C72.T6O5.Tests.not_NFi_diagM
#print axioms C72.T6O5.Tests.key_lt_pattern_revRow
#print axioms C72.T6O5.Tests.key_frobRow
#print axioms C72.T6O5.Tests.collImages_frobRow
#print axioms C72.T6O5.Tests.scanIdx_three_two
