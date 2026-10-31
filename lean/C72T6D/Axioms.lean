import C72T6D.Bridge
import C72T6D.CosetTable
import C72T6D.Basis
import C72T6D.Fin72

/-!
# Axiom report for the T6 order-2 additions (C72T6D)

The output of the `#print axioms` commands below is the axiom report. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

-- From the search to H_D k and Theorem D (C72T6D/Bridge.lean)
#print axioms C72.T6.H_D_of_search
#print axioms C72.T6.thmD_of_search

-- The table of the coset rule (C72T6D/CosetTable.lean)
#print axioms C72.T6.syn_formAct_coset
#print axioms C72.T6.coset_rule_table

-- Bad(y) and (diag) on a basis (C72T6D/Basis.lean)
#print axioms C72.T6.forall_disjoint_iff_syn
#print axioms C72.T6.half_wt_add_of_selfDual
#print axioms C72.T6.diag_of_span
#print axioms C72.T6.InA0_of_span

-- Proposition 6.2 backward on Fin 72 (C72T6D/Fin72.lean)
#print axioms C72.T6.aOf_apply
#print axioms C72.T6.aStd_aStd
#print axioms C72.T6.aOf_mul_self
#print axioms C72.T6.aOf_ne
#print axioms C72.T6.orderOf_aOf
#print axioms C72.T6.contracted_map_orbitEquiv
#print axioms C72.T6.aOf_mem_Aut
#print axioms C72.T6.prop62_converse_fin72
