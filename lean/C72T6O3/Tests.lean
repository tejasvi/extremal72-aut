import C72T6O3.Lemma44
import C72T6O3.Prop43
import C72T6O3.Orders

/-!
# T6 (order 3) tests on explicit values

* The base configuration is the program's: `O₀` is line 1, entry 1 of `octdod.txt`; `p₆, p₇, p₈ = 7, 10, 12`;
  `q₁ = 5` is the smallest point outside `O₀`.
* `NormalForm` is not vacuous and not trivial: for `c = (0, 1, 2, 3, 4)` the identity labelling of `G24` satisfies
  (N1)–(N3) (`normalForm_one`), so by Lemma 4.4 it is the only normal labelling of `G24` itself; `ρ` violates (N2)
  and `kq 6` violates (N3) (`not_normalForm_rho`, `not_normalForm_kq6`), although both give the same code `G24`.
* `M₂₄` is not trivial on the complement of `O₀`: `kq 6 ≠ 1`; and a transposition is not an automorphism of `G24`
  (`swap_not_mem_Aut`): `Aut G24` is a proper subgroup.
* The closure certificate needs `q₁`: from `p₁, …, p₆` alone the closure does not reach all points
  (`closeIter_without_q1`, the positive side of control C01).
-/

namespace C72.Three.M24.Tests

open Equiv Finset C72.Three.M24

/-- From `{0, 1, 2, 3, 4, 7}` (without `q₁`) two rounds of the closure do not reach all 24 points. -/
theorem closeIter_without_q1 : closeIter 2 159 ≠ FULL := by
  decide +kernel

/-- The five coordinates `0, 1, 2, 3, 4`. -/
def c0 : Fin 5 → Fin 24 :=
  fun i => bp i

theorem c0_injective : Function.Injective c0 := fun i j hij =>
  Fin.ext (by have := congrArg Fin.val hij; simp only [c0] at this; rwa [bp_val, bp_val] at this)

/-- The identity labelling of `G24` is in normal form for `c = (0, 1, 2, 3, 4)`. -/
theorem normalForm_one : NormalForm c0 1 := by
  refine ⟨fun i => rfl, ⟨by decide, by decide⟩, ?_, ?_⟩
  · show (5 : Fin 24) ∉ O0.map (1 : Perm (Fin 24)).toEmbedding
    rw [show (5 : Fin 24) = (1 : Perm (Fin 24)).toEmbedding 5 from rfl, Finset.mem_map']
    exact q1_spec.1
  · intro y hy
    by_contra hlt
    rw [not_le] at hlt
    apply hy
    rw [show y = (1 : Perm (Fin 24)).toEmbedding y from rfl, Finset.mem_map']
    exact q1_spec.2 y hlt

/-- Hence the identity is the only labelling of `G24` in normal form for `c = (0, 1, 2, 3, 4)`. -/
theorem unique_normal_G24 (π : Perm (Fin 24)) (hπ : G24.map (permute π).toLinearMap = G24)
    (hN : NormalForm c0 π) : π = 1 := by
  have h1 : (1 : Perm (Fin 24))⁻¹ * π ∈ Aut G24 := by
    rw [inv_one, one_mul, mem_Aut]
    exact hπ
  exact (lemma44_unique h1 normalForm_one hN).symm

/-- `ρ` gives the code `G24` but violates (N2). -/
theorem not_normalForm_rho : ¬ NormalForm c0 rho := by
  intro h
  have h2 : rho 7 < rho 12 := h.2.1.2
  rw [rho_spec.2.2.1, rho_spec.2.2.2.2] at h2
  exact absurd h2 (by decide)

/-- `kq 6 ∈ K` gives the code `G24` and satisfies (N1) and (N2) but violates (N3). -/
theorem not_normalForm_kq6 : ¬ NormalForm c0 (kq 6) := by
  intro h
  obtain ⟨_, hfix, hkq⟩ := kq_spec 6 (by rw [O0_eq]; decide)
  have h3 := h.2.2.2 (show (5 : Fin 24) ∈ {y | y ∉ O0.map (kq 6).toEmbedding} from by
    intro h5
    rw [Finset.mem_map] at h5
    obtain ⟨w, hw, hwq⟩ := h5
    rw [Equiv.coe_toEmbedding, hfix w hw] at hwq
    rw [hwq] at hw
    exact q1_spec.1 hw)
  rw [show kq 6 q1 = 6 from hkq] at h3
  exact absurd h3 (by decide)

theorem kq6_ne_one : kq 6 ≠ 1 := by
  intro h
  have := (kq_spec 6 (by rw [O0_eq]; decide)).2.2
  rw [h, Perm.one_apply] at this
  exact absurd this (by decide)

/-- The transposition `(0 1)` is not an automorphism of `G24`. -/
theorem swap_not_mem_Aut : Equiv.swap (0 : Fin 24) 1 ∉ Aut G24 := by
  intro h
  have h0 : g24gen 0 ∈ G24 := Submodule.subset_span ⟨0, rfl⟩
  have hmem := G24.add_mem (permute_mem_of_mem_Aut h h0) h0
  have hw : wt (permute (Equiv.swap (0 : Fin 24) 1) (g24gen 0) + g24gen 0) = 2 := by
    decide +kernel
  rcases G24_wt hmem with h' | h' | h' | h' | h' <;> omega

end C72.Three.M24.Tests
