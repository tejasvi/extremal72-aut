import C72T6K.Prop37
import C72T6.Toy

/-!
# T6: tests for the Klein case

On the toy code `Y4 = {(a, a, b, b)}` the permutation `β = (0 2)(1 3)` is a fixed-point-free involution in `Aut(Y4)`
(`βT`), the form `B4` lies in `A(Y4, β)` (`test_InA_toy`), and `aStd`, `liftP β` form a Klein pair of fixed-point-free
involutions in `Aut(C_{B4})` (`test_kleinPair_toy`): the hypotheses of `kleinPair_CB` and `prop37_converse` can be met.
`D_{{0, 1}}` (one element of each orbit `{0, 2}`, `{1, 3}`) and `D_{{0, 2}}` (a union of orbits) are `β`-invariant
(`test_DT_transversal`, `test_DT_invariant`).
-/

namespace C72.T6.KleinTests

open C72 C72.T4 C72.T6 C72.T6.Toy Equiv

/-- `β = (0 2)(1 3)`. -/
def β4 : Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem β4_symm_0 : β4.symm 0 = 2 := by decide
theorem β4_symm_1 : β4.symm 1 = 3 := by decide
theorem β4_symm_2 : β4.symm 2 = 0 := by decide
theorem β4_symm_3 : β4.symm 3 = 1 := by decide

theorem β4_mem_Aut : β4 ∈ Aut Y4 := by
  rw [mem_Aut_iff]
  intro x hx
  obtain ⟨h01, h23⟩ := mem_Y4.1 hx
  refine mem_Y4.2 ⟨?_, ?_⟩
  · rw [permute_apply, permute_apply, β4_symm_0, β4_symm_1]
    exact h23
  · rw [permute_apply, permute_apply, β4_symm_2, β4_symm_3]
    exact h01

/-- `β` as an element of `Aut(Y4)`. -/
def βT : Aut Y4 := ⟨β4, β4_mem_Aut⟩

theorem test_isFPFInv_β4 : IsFPFInv (βT : Perm (Fin 4)) :=
  ⟨Equiv.ext fun i => by fin_cases i <;> decide, by decide⟩

theorem B4_invariant : formAct βT B4 = B4 := by
  ext x x'
  show (autLin βT x : Fin 4 → ZMod 2) 0 * (autLin βT x' : Fin 4 → ZMod 2) 2 +
      (autLin βT x : Fin 4 → ZMod 2) 2 * (autLin βT x' : Fin 4 → ZMod 2) 0 =
    (x : Fin 4 → ZMod 2) 0 * (x' : Fin 4 → ZMod 2) 2 + (x : Fin 4 → ZMod 2) 2 * (x' : Fin 4 → ZMod 2) 0
  rw [autLin_coe, autLin_coe]
  show (x : Fin 4 → ZMod 2) (β4.symm 0) * (x' : Fin 4 → ZMod 2) (β4.symm 2) +
      (x : Fin 4 → ZMod 2) (β4.symm 2) * (x' : Fin 4 → ZMod 2) (β4.symm 0) = _
  rw [β4_symm_0, β4_symm_2]
  ring

theorem test_InA_toy : InA Y4 allOnes_mem_Y4 βT B4 :=
  ⟨B4_InA0, B4_invariant⟩

theorem test_kleinPair_toy :
    KleinPair (CB Y4 B4) aStd (liftP (βT : Perm (Fin 4))) ∧ (∀ p : Fin 4 × ZMod 2, aStd p ≠ p) ∧
      (∀ p, liftP (βT : Perm (Fin 4)) p ≠ p) ∧
      ∀ p, ((aStd : Perm (Fin 4 × ZMod 2)) * liftP (βT : Perm (Fin 4))) p ≠ p :=
  kleinPair_CB Y4_selfDual βT test_isFPFInv_β4 B4 B4_invariant

theorem test_DT_transversal : formAct βT (DT Y4 {0, 1}) = DT Y4 {0, 1} :=
  formAct_DT_of_transversal Y4_selfDual βT (by decide)

theorem test_DT_invariant : formAct βT (DT Y4 {0, 2}) = DT Y4 {0, 2} :=
  formAct_DT_of_invariant βT (by decide)

end C72.T6.KleinTests
