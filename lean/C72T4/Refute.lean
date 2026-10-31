import C72T4.Main

/-!
# T4: the model needs a self-dual contracted fixed code

The first-order Reed–Muller code `RM(1,3)` (the code `e8`) on the points `x ∈ 𝔽₂³`, with the points paired by the
translation `x ↦ x + (0,0,1)` (pair `i = x₁ + 2x₂`, `e = x₃`), is a Type II code on `Fin 4 × 𝔽₂` invariant under
`aStd`. Its contracted fixed code has dimension 3 on 4 coordinates, so it is not self-dual, and `RM(1,3)` is `C_B` for
no bilinear form `B` (`model_needs_selfDual`): the hypothesis `SelfDual Y` of `model` (which `H_L2` or the data supply)
carries weight. This is the positive side of control `C72T4Controls.T4C06ModelNeedsSelfDual`.
-/

namespace C72.T4.Refute

open C72 C72.T4 Module Finset

def ones4 : Fin 4 → ZMod 2 := ![1, 1, 1, 1]

def a4 : Fin 4 → ZMod 2 := ![0, 1, 0, 1]

def b4 : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- Generators of `RM(1,3)`: the affine functions `1`, `x₁`, `x₂`, `x₃`. -/
def rmGen : Fin 4 → (Fin 4 × ZMod 2 → ZMod 2) :=
  ![pv ones4 ones4, pv a4 a4, pv b4 b4, pv 0 ones4]

def RM : Submodule (ZMod 2) (Fin 4 × ZMod 2 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range rmGen)

theorem mem_RM_iff {c : Fin 4 × ZMod 2 → ZMod 2} :
    c ∈ RM ↔ ∃ p q r s : ZMod 2, p • rmGen 0 + q • rmGen 1 + r • rmGen 2 + s • rmGen 3 = c := by
  rw [RM, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f 0, f 1, f 2, f 3, by rw [← hf, Fin.sum_univ_four]⟩
  · rintro ⟨p, q, r, s, h⟩
    refine ⟨![p, q, r, s], ?_⟩
    rw [Fin.sum_univ_four]
    exact h

theorem rmGen_linearIndependent : LinearIndependent (ZMod 2) rmGen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  have key : ∀ p q r s : ZMod 2, p • rmGen 0 + q • rmGen 1 + r • rmGen 2 + s • rmGen 3 = 0 →
      p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
    decide
  obtain ⟨h0, h1, h2, h3⟩ := key _ _ _ _ hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem RM_le_dual : RM ≤ dual RM := by
  rw [RM, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨j, rfl⟩
  revert i j
  decide

theorem RM_typeII : TypeII RM := by
  refine ⟨selfDual_of_le_of_two_mul_finrank RM_le_dual ?_, fun x hx => ?_⟩
  · rw [RM, finrank_span_eq_card rmGen_linearIndependent, Fintype.card_fin]
    rfl
  · obtain ⟨p, q, r, s, rfl⟩ := mem_RM_iff.1 hx
    clear hx
    revert p q r s
    decide

theorem RM_inv : ∀ c ∈ RM, permute aStd c ∈ RM := by
  intro c hc
  have h : RM.map (permute (aStd : Equiv.Perm (Fin 4 × ZMod 2))).toLinearMap ≤ RM := by
    rw [RM, Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    show permute aStd (rmGen i) ∈ RM
    rw [mem_RM_iff]
    revert i
    decide
  exact h (Submodule.mem_map_of_mem hc)

theorem a4_mem_Yof : a4 ∈ Yof RM :=
  Submodule.subset_span ⟨1, rfl⟩

theorem b4_mem_Yof : b4 ∈ Yof RM :=
  Submodule.subset_span ⟨2, rfl⟩

/-- `σ(RM) ⊆ {0, 𝟙}`. -/
theorem sigma_RM (c : Fin 4 × ZMod 2 → ZMod 2) (hc : c ∈ RM) : sigmaL c ∈ Submodule.span (ZMod 2) {ones4} := by
  have h : RM.map sigmaL ≤ Submodule.span (ZMod 2) {ones4} := by
    rw [RM, Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    rw [Submodule.mem_span_singleton]
    revert i
    decide
  exact h (Submodule.mem_map_of_mem hc)

theorem a4_not_mem_span_ones : a4 ∉ Submodule.span (ZMod 2) {ones4} := by
  rw [Submodule.mem_span_singleton]
  decide

/-- If the contracted fixed code of `RM(1,3)` were self-dual, `a4` and `b4` would be orthogonal. -/
theorem orthogonal_of_selfDual_Yof_RM (h : SelfDual (Yof RM)) : a4 ⬝ᵥ b4 = 0 :=
  dotProduct_eq_zero_of_selfDual h a4_mem_Yof b4_mem_Yof

theorem not_selfDual_Yof_RM : ¬ SelfDual (Yof RM) := by
  intro h
  have := orthogonal_of_selfDual_Yof_RM h
  revert this
  decide

/-- **The model needs `Y` self-dual.** `RM(1,3)` is Type II and invariant under `aStd`, its contracted fixed code is
not self-dual, and it is `C_B` for no bilinear form `B` on that code. -/
theorem model_needs_selfDual :
    TypeII RM ∧ (∀ c ∈ RM, permute aStd c ∈ RM) ∧ ¬ SelfDual (Yof RM) ∧
      ¬ ∃ B : LinearMap.BilinForm (ZMod 2) (Yof RM), CB (Yof RM) B = RM := by
  refine ⟨RM_typeII, RM_inv, not_selfDual_Yof_RM, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨z, hz⟩ := exists_dotProduct_eq (B ⟨a4, a4_mem_Yof⟩)
  have hmem : pv z (z + a4) ∈ RM := by
    rw [← hB]
    exact mem_CB.2 ⟨⟨a4, a4_mem_Yof⟩, z, hz, rfl⟩
  have hs := sigma_RM _ hmem
  have hsig : sigmaL (pv z (z + a4)) = a4 := by
    rw [sigmaL_pv]
    funext i
    simp only [Pi.add_apply]
    generalize z i = u
    generalize a4 i = v
    revert u v
    decide
  rw [hsig] at hs
  exact a4_not_mem_span_ones hs

end C72.T4.Refute
