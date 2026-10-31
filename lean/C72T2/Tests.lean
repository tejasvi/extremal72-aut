import C72T2.TheoremB
import Mathlib.Tactic.NormNum.Prime

/-!
# T2 tests on explicit values and refutations of altered statements

* The dictionary of Section 4.1: `ψ(1) = 011`, `ψ(ω) = 101`, `ψ(ω̄) = 110`, `ω³ = 1`; the conjugation matters:
  with the bilinear product instead of the Hermitian one the trace identity is false (`refute_trace_bilinear`).
* The labelling of Section 4.1: `σ` maps `(k, b)` to `(k, b + 1)` (here `3k + b ↦ 3k + b + 1 mod 3`), and on
  an explicit word `σ` acts on `φ(e)` as multiplication by `ω`, not by `ω̄` (`sigma3_phi_example`,
  `refute_action_wb`).
* Definitions on explicit values: Lemma 4.1 on a word of weight 22; `MinWt G24 12` is false.
* The predicates can be satisfied: `G24` is Type II with minimum weight 8, has a word of weight 8, and its
  automorphism group contains the 23-cycle `i ↦ i + 1 mod 23` (fixing 23), so `Aut C = ⊥` is a real claim; the code
  of length 2 spanned by `(1, ω)` is Hermitian self-dual but not self-orthogonal for the bilinear product.

Every check is a kernel `decide` or an elementary proof.
-/

namespace C72.Three.Tests

open Equiv Finset F4

/-! ## `𝔽₄` and `ψ` -/

/-- The paper's dictionary: `ψ(1) = 011`, `ψ(ω) = 101`, `ψ(ω̄) = 110`. -/
theorem psi_values : psi 1 = ![0, 1, 1] ∧ psi F4.w = ![1, 0, 1] ∧ psi F4.wb = ![1, 1, 0] :=
  ⟨rfl, rfl, rfl⟩

/-- `ω` has multiplicative order 3, `ω̄ = ω²`, and `𝔽₄` has characteristic 2. -/
theorem w_order : F4.w ^ 3 = 1 ∧ F4.w ≠ 1 ∧ F4.w ^ 2 = F4.wb ∧ ((2 : ℕ) : F4) = 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [natCast_eq]
  rfl

/-- With the bilinear product `u v` instead of the Hermitian `u v̄`, the trace identity fails
(at `u = v = ω`: `⟨ψ(ω), ψ(ω)⟩ = 0` but `Tr(ω²) = 1`). -/
theorem refute_trace_bilinear : ¬ ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * v) := by
  intro h
  have := h F4.w F4.w
  revert this
  decide

/-! ## The labelling and the action of `σ` -/

/-- `σ` on the first and last cycles: `0 ↦ 1 ↦ 2 ↦ 0` and `69 ↦ 70 ↦ 71 ↦ 69`. -/
theorem sigma3_values : sigma3 0 = 1 ∧ sigma3 1 = 2 ∧ sigma3 2 = 0 ∧ sigma3 69 = 70 ∧ sigma3 70 = 71 ∧
    sigma3 71 = 69 := by
  decide +kernel

/-- `φ(e)` for `e = (1, 0, …, 0)` is `011` on the first cycle, and `φ(e) σ = φ(ω e)` is `101` there. -/
theorem sigma3_phi_example :
    permute sigma3 (phi (Pi.single 0 1)) = phi (Pi.single 0 F4.w) ∧
      phi (Pi.single 0 1) (idx 0 0) = 0 ∧ phi (Pi.single 0 1) (idx 0 1) = 1 ∧
      phi (Pi.single 0 1) (idx 0 2) = 1 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [permute_sigma3_phi]
  congr 1
  funext k
  by_cases hk : k = 0
  · subst hk
    rfl
  · simp [hk]

/-- `σ` does not act as multiplication by `ω̄` (the conjugate convention). -/
theorem refute_action_wb : ¬ ∀ e : Fin 24 → F4, permute sigma3 (phi e) = phi (F4.wb • e) := by
  intro h
  have h1 := h (Pi.single 0 1)
  rw [permute_sigma3_phi] at h1
  have h2 := congrFun h1 (idx 0 1)
  revert h2
  decide

/-! ## Lemma 4.1 on explicit words -/

/-- `g = g24gen 0` has weight 8 and `e = (1, 0, …, 0)` meets it in one point, so Lemma 4.1 gives
`3 · 8 + 2 · 1 - 4 · 1 = 22`. -/
theorem lemma41_example :
    wt (g24gen 0) = 8 ∧ wt (Pi.single 0 1 : Fin 24 → F4) = 1 ∧
      #(supp (g24gen 0) ∩ supp (Pi.single 0 1 : Fin 24 → F4)) = 1 ∧
      wt (triple (g24gen 0) + phi (Pi.single 0 1)) = 22 := by
  decide +kernel

/-! ## `G24` -/

/-- `MinWt G24 12` is false: `MinWt` is not satisfied vacuously. -/
theorem not_minWt_G24_12 : ¬ MinWt G24 12 := by
  intro h
  have h8 := h (g24gen 0) (Submodule.subset_span ⟨0, rfl⟩) (by decide +kernel)
  have hw : wt (g24gen 0) = 8 := by decide +kernel
  omega

/-- The 23-cycle `i ↦ i + 1 (mod 23)` fixing 23 (T1's `stdPerm 1 23 1`). -/
def tau23 : Perm (Fin 24) :=
  stdPerm 1 23 1 rfl

theorem tau23_values : tau23 0 = 1 ∧ tau23 21 = 22 ∧ tau23 22 = 0 ∧ tau23 23 = 23 := by
  decide +kernel

/-- The cyclic shift maps every generator into `G24` (the code is cyclic on the first 23 coordinates). -/
theorem tau23_gen_orth : ∀ s j : Fin 12, permute tau23 (g24gen s) ⬝ᵥ g24gen j = 0 := by
  decide +kernel

theorem tau23_mem_Aut : tau23 ∈ Aut G24 := by
  apply mem_Aut_of_map_le
  rw [G24, Submodule.map_span_le]
  rintro _ ⟨s, rfl⟩
  exact mem_G24_of_orth (tau23_gen_orth s)

/-- `G24` is Type II with minimum weight exactly 8 and has a nontrivial automorphism: the predicates of T2 are
satisfiable and `Aut C = ⊥` is not automatic. -/
theorem G24_check : TypeII G24 ∧ MinWt G24 8 ∧ (∃ x ∈ G24, wt x = 8) ∧ Aut G24 ≠ ⊥ := by
  refine ⟨G24_typeII, G24_minWt, G24_wt8, fun h => ?_⟩
  have hmem := tau23_mem_Aut
  rw [h, Subgroup.mem_bot] at hmem
  have h0 : tau23 0 = 1 := by decide +kernel
  rw [hmem, Perm.one_apply] at h0
  exact absurd h0 (by decide)

/-! ## A Hermitian self-dual code -/

/-- The code of length 2 spanned by `(1, ω)`. -/
def E2 : Submodule F4 (Fin 2 → F4) :=
  Submodule.span F4 {![1, F4.w]}

/-- `E2` is Hermitian self-dual: `⟨(1, ω), (1, ω)⟩_H = 1 + ω ω̄ = 0`, and its Hermitian dual is spanned by
`(1, ω)`. -/
theorem E2_hselfDual : HSelfDual E2 := by
  apply le_antisymm
  · rw [E2, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_hdual_span]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    decide
  · intro x hx
    rw [E2, mem_hdual_span] at hx
    have h := hx _ (Set.mem_singleton _)
    have hx' : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    have key : ∀ x0 x1 : F4, hform ![x0, x1] ![1, F4.w] = 0 → x0 • ![1, F4.w] = ![x0, x1] := by
      decide
    rw [E2, Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    rw [hx'] at h ⊢
    exact key _ _ h

/-- For the bilinear product the generator of `E2` is not self-orthogonal: `1 + ω² = ω ≠ 0`. -/
theorem E2_not_bilinear : ∑ i : Fin 2, (![1, F4.w] : Fin 2 → F4) i * (![1, F4.w] : Fin 2 → F4) i ≠ 0 := by
  decide

end C72.Three.Tests
