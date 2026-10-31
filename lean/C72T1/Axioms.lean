import C72T1.Defs
import C72T1.Final
import C72T1.Paper
import C72T1.Decomp
import C72T1.Labelling
import C72T1.Tests
import C72T1.Refute

/-!
# Axiom report for the T1 theorems

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- Definitions layer
#print axioms C72.permute_apply_self
#print axioms C72.mem_Aut_map_permute_iff
#print axioms C72.Aut_map_permute
#print axioms C72.wt_permute
#print axioms C72.dotProduct_permute
#print axioms C72.dual_map_permute
#print axioms C72.SelfDual.map_permute
#print axioms C72.finrank_add_finrank_dual
#print axioms C72.SelfDual.two_mul_finrank
#print axioms C72.selfDual_of_le_of_two_mul_finrank
#print axioms C72.mem_Aut_iff
#print axioms C72.mem_dual_span
#print axioms C72.TypeII.map_permute
#print axioms C72.MinWt.map_permute
#print axioms C72.Ext72.map_permute
#print axioms C72.Ext72.finrank

-- Final deduction
#print axioms C72.card_Aut_pos
#print axioms C72.eq_bot_of_no_small_prime_orders
#print axioms C72.noInv_of
#print axioms C72.main_of_parts
#print axioms C72.main_of_cited

-- Paper-form statements
#print axioms C72.paper_action
#print axioms C72.ext72_iff_paper
#print axioms C72.mem_Aut_iff_paper
#print axioms C72.paperMain_of_cited
#print axioms C72.primes_of_order_le_five
#print axioms C72.H_primes_of_orders
#print axioms C72.hyps_of_no_extremal

-- Decomposition for an odd prime
#print axioms C72.card_cyc
#print axioms C72.sum_cyc_eq_sum_range
#print axioms C72.mem_Esub_iff
#print axioms C72.Fsub_sup_Esub
#print axioms C72.Fsub_inf_Esub
#print axioms C72.Fsub_orthogonal_Esub
#print axioms C72.decomposition
#print axioms C72.Fsub_eq_map_contracted
#print axioms C72.expand_dotProduct
#print axioms C72.contracted_selfDual

-- Labelling
#print axioms C72.labelling
#print axioms C72.exists_relabel

-- Tests (the action convention and definition checks)
#print axioms C72.Tests.permute_c3_single
#print axioms C72.Tests.permute_c3_word
#print axioms C72.Tests.map_span_c3
#print axioms C72.Tests.permute_mul_example
#print axioms C72.Tests.swap01_mem_Aut_C4
#print axioms C72.Tests.swap12_not_mem_Aut_C4
#print axioms C72.Tests.stdPerm_2_3_1
#print axioms C72.Tests.stdPerm_14_5_2
#print axioms C72.Tests.stdPerm_24_3_0
#print axioms C72.Tests.stdPerm_36_2_0
#print axioms C72.Tests.e8_check
#print axioms C72.Tests.Aut_e8_ne_bot
#print axioms C72.Tests.rep2_selfDual
#print axioms C72.Tests.rep2_even
#print axioms C72.Tests.rep2_not_typeII

-- Refutations of weakened statements (positive side of the controls)
#print axioms C72.Refute.core_needs_primes
#print axioms C72.Refute.core_needs_no_order5
#print axioms C72.Refute.core_needs_no_order3
#print axioms C72.Refute.core_needs_no_order2
#print axioms C72.Refute.decomposition_needs_odd
#print axioms C72.Refute.contracted_needs_selfDual
