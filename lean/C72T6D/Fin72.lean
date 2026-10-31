import C72T6.Converse
import C72T4.Main

/-!
# T6, order 2: Proposition 6.2 backward on `Fin 72`

For a labelling `e : ι ≃ κ × 𝔽₂`, `aOf e = e⁻¹ aStd e` is a fixed-point-free involution of `ι` (`aOf_mul_self`, `aOf_ne`),
its orbits are the pairs (`orbitEquiv e : Orbits (aOf e) ≃ κ`), and the contracted fixed code of `aOf e` on a code moved
from `κ × 𝔽₂` to `ι` is the contracted fixed code `Yof` of the original code (`contracted_map_orbitEquiv`). With
`prop62_converse` this gives the backward direction of Proposition 6.2 as the paper reads it, on `Fin 72`
(`prop62_converse_fin72`), with minimum weight at least 16.
-/

namespace C72.T6

open C72 C72.T4 Module Finset Equiv

variable {ι κ : Type*}

/-- `a = e⁻¹ aStd e` on `ι`, for a labelling `e : ι ≃ κ × 𝔽₂`. -/
def aOf (e : ι ≃ κ × ZMod 2) : Perm ι :=
  e.symm.permCongr aStd

theorem aOf_apply (e : ι ≃ κ × ZMod 2) (j : ι) : aOf e j = e.symm (aStd (e j)) :=
  rfl

theorem aStd_aStd (p : κ × ZMod 2) : aStd (aStd p) = p := by
  obtain ⟨i, f⟩ := p
  show (i, f + 1 + 1) = (i, f)
  rw [add_assoc, zmod2_add_self', add_zero]

theorem aOf_mul_self (e : ι ≃ κ × ZMod 2) : aOf e * aOf e = 1 := by
  ext x
  show e.symm (aStd (e (e.symm (aStd (e x))))) = x
  rw [Equiv.apply_symm_apply, aStd_aStd, Equiv.symm_apply_apply]

theorem aOf_ne (e : ι ≃ κ × ZMod 2) (j : ι) : aOf e j ≠ j := by
  intro h
  have h1 : aStd (e j) = e j := by
    have h' := congrArg e h
    rwa [aOf_apply, Equiv.apply_symm_apply] at h'
  have h2 := congrArg Prod.snd h1
  change (e j).2 + 1 = (e j).2 at h2
  exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _ h2

theorem orderOf_aOf [Nonempty ι] (e : ι ≃ κ × ZMod 2) : orderOf (aOf e) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, aOf_mul_self]
  · intro h
    obtain ⟨j⟩ := ‹Nonempty ι›
    exact aOf_ne e j (by rw [h]; rfl)

/-- The orbits of `aOf e` are the pairs: the orbit of `j` goes to `(e j).1`. -/
noncomputable def orbitEquiv [Fintype ι] (e : ι ≃ κ × ZMod 2) : Orbits (aOf e) ≃ κ where
  toFun := Quotient.lift (fun j => (e j).1) (fun j j' h => by
    rcases sameCycle_involution (aOf_mul_self e) h with h' | h'
    · rw [h']
    · rw [h', aOf_apply, Equiv.apply_symm_apply]
      rfl)
  invFun i := toOrbit (aOf e) (e.symm (i, 0))
  left_inv ω := by
    induction ω using Quotient.inductionOn with
    | h j =>
      show toOrbit (aOf e) (e.symm ((e j).1, 0)) = toOrbit (aOf e) j
      rcases zmod2_cases (e j).2 with h | h
      · have hp : ((e j).1, (0 : ZMod 2)) = e j := Prod.ext rfl h.symm
        rw [hp, Equiv.symm_apply_apply]
      · have hp : ((e j).1, (0 : ZMod 2)) = aStd (e j) := by
          refine Prod.ext rfl ?_
          show (0 : ZMod 2) = (e j).2 + 1
          rw [h]
          decide
        rw [hp, ← aOf_apply, toOrbit_apply]
  right_inv i := by
    show (e (e.symm (i, 0))).1 = i
    rw [Equiv.apply_symm_apply]

private theorem pv_self_apply_loc (u : κ → ZMod 2) (p : κ × ZMod 2) : pv u u p = u p.1 := by
  unfold pv
  split_ifs <;> rfl

/-- The contracted fixed code of `aOf e` on `C` moved to `ι` is `Yof C`, moved by `orbitEquiv e`. -/
theorem contracted_map_orbitEquiv [Fintype ι] (e : ι ≃ κ × ZMod 2) (C : Submodule (ZMod 2) (κ × ZMod 2 → ZMod 2)) :
    (contracted (aOf e) (C.map (reindex e.symm).toLinearMap)).map (reindex (orbitEquiv e)).toLinearMap = Yof C := by
  ext u
  rw [mem_map_reindex, mem_contracted, mem_map_reindex, Equiv.symm_symm, mem_Yof]
  have h : reindex e (expand (aOf e) (reindex (orbitEquiv e).symm u)) = pv u u := by
    funext p
    rw [reindex_apply, expand_apply, reindex_apply, Equiv.symm_symm, pv_self_apply_loc]
    show u ((e (e.symm p)).1) = u p.1
    rw [Equiv.apply_symm_apply]
  rw [h]

private theorem permute_permCongr_reindex_loc {α β : Type*} (e : α ≃ β) (b : Perm α) (c : α → ZMod 2) :
    permute (e.permCongr b) (reindex e c) = reindex e (permute b c) := by
  funext x
  rw [permute_apply, reindex_apply, reindex_apply, permute_apply]
  congr 1
  simp only [Equiv.permCongr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem aOf_mem_Aut [Fintype ι] (e : ι ≃ κ × ZMod 2) {C : Submodule (ZMod 2) (κ × ZMod 2 → ZMod 2)}
    (ha : ∀ c ∈ C, permute aStd c ∈ C) : aOf e ∈ Aut (C.map (reindex e.symm).toLinearMap) := by
  rw [mem_Aut_iff]
  rintro _ ⟨c, hc, rfl⟩
  show permute (aOf e) (reindex e.symm c) ∈ _
  rw [aOf, permute_permCongr_reindex_loc]
  exact Submodule.mem_map_of_mem (ha c hc)

/-- **Proposition 6.2, backward, on `Fin 72`.** A form of `A_0(Y_k)` that is not ruled out gives a Type II code of length
72 with minimum weight at least 16 and a fixed-point-free involution whose contracted fixed code is equivalent to `Y_k`
(the minimum weight 8 of `Y_k` is a premise). -/
theorem prop62_converse_fin72 (k : Fin 41) (B : LinearMap.BilinForm (ZMod 2) (Yc k))
    (hA : InA0 (Yc k) (allOnes_mem_Yc k) B) (hnr : ¬ RuledOut (Yc k) B) (h8 : MinWt (Yc k) 8) :
    ∃ C : Code 72, TypeII C ∧ MinWt C 16 ∧ ∃ a ∈ Aut C, orderOf a = 2 ∧ (∀ i, a i ≠ i) ∧
      CodeEquiv (contracted a C) (Yc k) := by
  obtain ⟨hT, hM, ha, hY⟩ := prop62_converse k B hA hnr h8
  let e : Fin 72 ≃ Fin 36 × ZMod 2 := Fintype.equivOfCardEq (by simp)
  refine ⟨(CB (Yc k) B).map (reindex e.symm).toLinearMap, TypeII.map_reindex hT e.symm,
    MinWt.map_reindex hM e.symm, aOf e, aOf_mem_Aut e ha, orderOf_aOf e, aOf_ne e, orbitEquiv e, ?_⟩
  rw [contracted_map_orbitEquiv, hY]

end C72.T6
