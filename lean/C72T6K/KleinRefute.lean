import C72T6K.KleinTests
import C72T6.Refute

/-!
# T6: refutations behind the Klein-case controls

* `pair_form_needs_commute`: Lemma 3.4 (a) needs that `b` commutes with `a`: the swap `bK` of `(0, 1)` and `(1, 0)` on
  `Fin 2 × 𝔽₂` sends the pair `{(0, 0), (0, 1)}` to two different pairs.
* `liftP_needs_invariance`: Lemma 3.4 (c) needs `B` to be `β`-invariant: `Bn(x, x') = x₀x'₂` on `Y4` is not invariant under
  `β = (0 2)(1 3)` (`Bn(u1 β, u2 β) = 0 ≠ 1 = Bn(u1, u2)`), and the lift of `β` is not an automorphism of `C_{Bn}`.
* `transversal_needs_selfDual`: Lemma 3.5 (b) for a set with one element of each orbit needs `Y` self-dual: on the full
  space `𝔽₂²` with `β = (0 1)`, `D_{{0}}^β ≠ D_{{0}}`.
-/

namespace C72.T6.KleinRefute

open C72 C72.T4 C72.T6 C72.T6.Toy C72.T6.Refute C72.T6.KleinTests Equiv

/-- The swap of `(0, 1)` and `(1, 0)` on `Fin 2 × 𝔽₂`. -/
def bK : Perm (Fin 2 × ZMod 2) := Equiv.swap (0, 1) (1, 0)

theorem bK_apply_00 : (bK (0, 0)).1 = 0 := by decide

theorem bK_apply_01 : (bK (0, 1)).1 = 1 := by decide

/-- **Lemma 3.4 (a) needs `b a = a b`.** `bK` does not commute with `aStd`, and it is not of the form
`(i, e) ↦ (β i, e + t i)`. -/
theorem pair_form_needs_commute : bK * aStd ≠ aStd * bK ∧
    ¬ ∃ β : Perm (Fin 2), ∃ t : Fin 2 → ZMod 2, ∀ i e, bK (i, e) = (β i, e + t i) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' := congrArg (fun f : Perm (Fin 2 × ZMod 2) => (f (0, 0)).1) h
    change (bK (0, 1)).1 = (bK (0, 0)).1 at h'
    rw [bK_apply_00, bK_apply_01] at h'
    exact absurd h' (by decide)
  · rintro ⟨β, t, h⟩
    have h0 : (bK (0, 0)).1 = β 0 := congrArg Prod.fst (h 0 0)
    have h1 : (bK (0, 1)).1 = β 0 := congrArg Prod.fst (h 0 1)
    rw [bK_apply_00] at h0
    rw [bK_apply_01] at h1
    exact absurd (h0.trans h1.symm) (by decide)

/-- **Lemma 3.4 (c) needs invariance.** -/
theorem liftP_needs_invariance : formAct βT Bn ≠ Bn ∧ liftP (βT : Perm (Fin 4)) ∉ Aut (CB Y4 Bn) := by
  have h : formAct βT Bn ≠ Bn := by
    intro h
    have h' := congrArg (fun F : LinearMap.BilinForm (ZMod 2) Y4 => F u1 u2) h
    change (u1 : Fin 4 → ZMod 2) (β4.symm 0) * (u2 : Fin 4 → ZMod 2) (β4.symm 2) =
      (u1 : Fin 4 → ZMod 2) 0 * (u2 : Fin 4 → ZMod 2) 2 at h'
    rw [β4_symm_0, β4_symm_2] at h'
    exact absurd h' (by decide)
  exact ⟨h, fun hm => h ((liftP_mem_Aut_CB_iff βT Bn).1 hm)⟩

/-- The full space `𝔽₂²` and the swap of its two coordinates. -/
def βF : Aut (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) :=
  ⟨Equiv.swap 0 1, mem_Aut_iff.2 fun _ _ => Submodule.mem_top⟩

/-- The word `10` of `𝔽₂²`. -/
def y10 : (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := ⟨![1, 0], Submodule.mem_top⟩

/-- **Lemma 3.5 (b) for a transversal needs `Y` self-dual.** `{0}` contains one element of the orbit `{0, 1}`, and
`D_{{0}}^β(10, 10) = 0 ≠ 1 = D_{{0}}(10, 10)` on the full space. -/
theorem transversal_needs_selfDual : (∀ i, (βF : Perm (Fin 2)) i ∈ ({0} : Finset (Fin 2)) ↔ i ∉ ({0} : Finset (Fin 2))) ∧
    formAct βF (DT ⊤ {0}) ≠ DT ⊤ {0} := by
  refine ⟨by decide, fun h => ?_⟩
  have h' := congrArg (fun F : LinearMap.BilinForm (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) => F y10 y10) h
  change ∑ i ∈ ({0} : Finset (Fin 2)), (y10 : Fin 2 → ZMod 2) ((Equiv.swap (0 : Fin 2) 1).symm i) *
      (y10 : Fin 2 → ZMod 2) ((Equiv.swap (0 : Fin 2) 1).symm i) =
    ∑ i ∈ ({0} : Finset (Fin 2)), (y10 : Fin 2 → ZMod 2) i * (y10 : Fin 2 → ZMod 2) i at h'
  exact absurd h' (by decide)

end C72.T6.KleinRefute
