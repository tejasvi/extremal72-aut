import C72T5.Known

/-!
# Axiom report for the T5 theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- The Main Theorem from the twelve named hypotheses
#print axioms C72.mainTheorem
#print axioms C72.mainTheorem_paper

-- The hypotheses and the conclusion as stated (Iff.rfl pins)
#print axioms C72.H_primes_def
#print axioms C72.H_L1_def
#print axioms C72.H_L2_def
#print axioms C72.H_L3_def
#print axioms C72.H_CP5_def
#print axioms C72.H_CP3_def
#print axioms C72.H_16_def
#print axioms C72.H_Golay_def
#print axioms C72.H_LP_def
#print axioms C72.H_A_def
#print axioms C72.H_CB_def
#print axioms C72.H_D_def
#print axioms C72.conclusion_def

-- The length-48 analog of H_CB is false
#print axioms C72.T5.CB48.go_c0_0
#print axioms C72.T5.CB48.go_c0_1
#print axioms C72.T5.CB48.go_c0_2
#print axioms C72.T5.CB48.go_c0_3
#print axioms C72.T5.CB48.go_all
#print axioms C72.T5.CB48.go_sound
#print axioms C72.T5.CB48.E48_leaf
#print axioms C72.T5.CB48.E48_minWt
#print axioms C72.T5.CB48.E48_hselfDual
#print axioms C72.T5.CB48.origRow_mem
#print axioms C72.T5.CB48.tet_of_isTetrad
#print axioms C72.T5.CB48.oct_of_isOctad
#print axioms C72.T5.CB48.tetStd_check
#print axioms C72.T5.CB48.octStd_check
#print axioms C72.T5.not_H_CB48

-- Definition checks on known codes
#print axioms C72.T5.half_wt_add
#print axioms C72.T5.A0_nonempty
#print axioms C72.T5.hyps_of_no_extremal
#print axioms C72.T5.known_codes
