import C72T6O3.M24

/-!
# T6 (order 3): Lemma 4.4 of the paper (the labelling normal form)

Fix the octad `O₀` of `G24` with points `p₁ < ⋯ < p₈`, the point `q₁ ∉ O₀` (the base configuration of the
point-placement program, `C72T6O3.M24`) and five distinct coordinates `c₁, …, c₅` of `E` (`c`, injective; the
paper takes `c₁ < ⋯ < c₅`, which the proof does not use).

**Lemma 4.4.** Every Golay code on the coordinates of `E` is `π(G24)` for exactly one bijection `π` with
* (N1) `π(pᵢ) = cᵢ` for `i = 1, …, 5`,
* (N2) `π(p₆) < π(p₇)` and `π(p₆) < π(p₈)`,
* (N3) `π(q₁)` is the smallest coordinate outside `π(O₀)` (`NormalForm`, `lemma44`).

The proof is the paper's, in the corrected form of the final version: given `π`, choose `m₁ ∈ M₂₄` with
`π m₁(pᵢ) = cᵢ` (5-transitivity); the elements of `π m₁ H` satisfy (N1) and permute the values at `p₆, p₇, p₈`
cyclically, so exactly one coset `π m₁ h₀ K` satisfies (N2); on this coset the value at `q₁` runs once through the
coordinates outside `π m₁(O₀)`, the common image of `O₀` under the elements of `π m₁ H` (`map_O0_mul_InH`),
because `K` is regular on the complement of `O₀`; so exactly one element also satisfies (N3). Uniqueness: if `π`
and `π m` both satisfy (N1)–(N3), then `m ∈ H` by (N1), `m ∈ K` by (N2) and `m = 1` by (N3).
-/

namespace C72.Three.M24

open Equiv Finset

/-- (N1)–(N3) of Lemma 4.4 for the bijection `π` from the points of `G24` to the coordinates of `E` and the five
coordinates `c`. -/
def NormalForm (c : Fin 5 → Fin 24) (π : Perm (Fin 24)) : Prop :=
  (∀ i : Fin 5, π (bp i) = c i) ∧ (π (pp 5) < π (pp 6) ∧ π (pp 5) < π (pp 7)) ∧
    IsLeast {y | y ∉ O0.map π.toEmbedding} (π q1)

/-- `π(G24) = π₀(G24)` exactly when `π = π₀ m` with `m ∈ M₂₄`. -/
theorem map_permute_eq_iff {π π₀ : Perm (Fin 24)} :
    G24.map (permute π).toLinearMap = G24.map (permute π₀).toLinearMap ↔ π₀⁻¹ * π ∈ Aut G24 := by
  constructor
  · intro h
    rw [mem_Aut, map_permute_mul, h, ← map_permute_mul, inv_mul_cancel, map_permute_one]
  · intro h
    have hπ : π = π₀ * (π₀⁻¹ * π) := by group
    rw [hπ, map_permute_mul, mem_Aut.1 h]

/-- Right multiplication by an element of `K` does not change the image of `O₀`. -/
theorem map_O0_mul_InK {σ k : Perm (Fin 24)} (hk : ∀ y ∈ O0, k y = y) :
    O0.map (σ * k).toEmbedding = O0.map σ.toEmbedding := by
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, Perm.mul_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [hk w hw]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [hk w hw]⟩

/-- Right multiplication by an element of `H` does not change the image of `O₀`: `π m₁(O₀)` is the common image
of `O₀` under the elements of `π m₁ H`. -/
theorem map_O0_mul_InH {σ h : Perm (Fin 24)} (hh : InH h) :
    O0.map (σ * h).toEmbedding = O0.map σ.toEmbedding := by
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, Perm.mul_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨h w, hh.apply_mem hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨h⁻¹ w, hh.inv.apply_mem hw, ?_⟩
    rw [Perm.inv_def, Equiv.apply_symm_apply]

/-- Existence in Lemma 4.4: some `π₀ m` (`m ∈ M₂₄`) satisfies (N1)–(N3). -/
theorem lemma44_exists (c : Fin 5 → Fin 24) (hc : Function.Injective c) (π₀ : Perm (Fin 24)) :
    ∃ π : Perm (Fin 24), π₀⁻¹ * π ∈ Aut G24 ∧ NormalForm c π := by
  -- (N1): `π₀ m₁` with `m₁(pᵢ) = π₀⁻¹(cᵢ)`, by 5-transitivity
  obtain ⟨m1, hm1, hm1i⟩ :=
    five_transitive (fun i => π₀.symm (c i)) (fun i j hij => hc (π₀.symm.injective hij))
  have hN1 : ∀ i, (π₀ * m1) (bp i) = c i := fun i => by
    rw [Perm.mul_apply, hm1i, Equiv.apply_symm_apply]
  -- (N2): a rotation `h₀ ∈ {1, ρ, ρ²}` puts the smallest of the three values at `p₆`
  have hr7 : rho 7 = 10 := rho_spec.2.2.1
  have hr10 : rho 10 = 12 := rho_spec.2.2.2.1
  have hr12 : rho 12 = 7 := rho_spec.2.2.2.2
  obtain ⟨h0, hh0, hN2⟩ : ∃ h0, InH h0 ∧
      (π₀ * m1 * h0) 7 < (π₀ * m1 * h0) 10 ∧ (π₀ * m1 * h0) 7 < (π₀ * m1 * h0) 12 := by
    set σ := π₀ * m1 with hσ
    have d1 : σ 7 ≠ σ 10 := fun h => absurd (σ.injective h) (by decide)
    have d2 : σ 7 ≠ σ 12 := fun h => absurd (σ.injective h) (by decide)
    have d3 : σ 10 ≠ σ 12 := fun h => absurd (σ.injective h) (by decide)
    rw [Ne, Fin.ext_iff] at d1 d2 d3
    by_cases ha : σ 7 < σ 10 ∧ σ 7 < σ 12
    · refine ⟨1, ⟨(Aut G24).one_mem, fun _ => rfl⟩, ?_⟩
      simpa only [mul_one] using ha
    · by_cases hb : σ 10 < σ 7 ∧ σ 10 < σ 12
      · refine ⟨rho, rho_InH, ?_⟩
        simp only [Perm.mul_apply, hr7, hr10, hr12]
        exact ⟨hb.2, hb.1⟩
      · refine ⟨rho ^ 2, rho_InH.pow 2, ?_⟩
        simp only [Perm.mul_apply, pow_two, hr7, hr10, hr12]
        simp only [Fin.lt_def, not_and_or, not_lt] at ha hb ⊢
        omega
  -- (N3): on the coset, the value at `q₁` runs through the coordinates outside `π₀ m₁(O₀)`
  have himg : O0.map (π₀ * m1 * h0).toEmbedding = O0.map (π₀ * m1).toEmbedding := map_O0_mul_InH hh0
  let S := (Finset.univ : Finset (Fin 24)).filter fun y => y ∉ O0.map (π₀ * m1).toEmbedding
  have hS : S.Nonempty := by
    refine ⟨(π₀ * m1) q1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    rw [show (π₀ * m1) q1 = (π₀ * m1).toEmbedding q1 from rfl, Finset.mem_map']
    exact q1_spec.1
  let y0 := S.min' hS
  have hy0 : y0 ∉ O0.map (π₀ * m1).toEmbedding := (Finset.mem_filter.1 (S.min'_mem hS)).2
  let x := (π₀ * m1 * h0).symm y0
  have hx : x ∉ O0 := by
    intro hxO
    apply hy0
    rw [← himg, Finset.mem_map]
    exact ⟨x, hxO, by simp [x]⟩
  obtain ⟨hk, hkfix, hkq⟩ := kq_spec x hx
  refine ⟨π₀ * m1 * h0 * kq x, ?_, ?_, ?_, ?_⟩
  · have he : π₀⁻¹ * (π₀ * m1 * h0 * kq x) = m1 * h0 * kq x := by group
    rw [he]
    exact (Aut G24).mul_mem ((Aut G24).mul_mem hm1 hh0.1) hk
  · intro i
    rw [Perm.mul_apply, hkfix _ (bp_mem_O0 i), Perm.mul_apply, hh0.2, hN1]
  · have h7 : (7 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
    have h10 : (10 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
    have h12 : (12 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
    show (π₀ * m1 * h0 * kq x) 7 < (π₀ * m1 * h0 * kq x) 10 ∧
      (π₀ * m1 * h0 * kq x) 7 < (π₀ * m1 * h0 * kq x) 12
    rw [Perm.mul_apply, Perm.mul_apply (π₀ * m1 * h0) (kq x) 10, Perm.mul_apply (π₀ * m1 * h0) (kq x) 12,
      hkfix 7 h7, hkfix 10 h10, hkfix 12 h12]
    exact hN2
  · rw [map_O0_mul_InK hkfix, himg, Perm.mul_apply, hkq]
    have hxy : (π₀ * m1 * h0) x = y0 := Equiv.apply_symm_apply _ y0
    rw [hxy]
    exact ⟨hy0, fun y hy => Finset.min'_le S y (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩)⟩

/-- Uniqueness in Lemma 4.4: if `π` and `π m` (`m ∈ M₂₄`) both satisfy (N1)–(N3), then `m = 1`. -/
theorem lemma44_unique {c : Fin 5 → Fin 24} {π π' : Perm (Fin 24)} (hm : π⁻¹ * π' ∈ Aut G24)
    (hN : NormalForm c π) (hN' : NormalForm c π') : π = π' := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = π⁻¹ * π' := ⟨_, rfl⟩
  rw [← hmdef] at hm
  have hπ' : π' = π * m := by
    rw [hmdef]
    group
  -- `m ∈ H`, by (N1)
  have hH : InH m := ⟨hm, fun j => by
    have h1 := hN.1 j
    have h2 := hN'.1 j
    rw [hπ', Perm.mul_apply] at h2
    exact π.injective (h2.trans h1.symm)⟩
  -- `m ∈ K`, by (N2)
  obtain ⟨j, hj3, hj⟩ := InH_eq_rho_pow_mul hH
  have hmO : ∀ y ∈ O0, m y = (rho ^ j) y := fun y hy => by
    have h := hj.2 y hy
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq] at h
    exact h
  have h7 : (7 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have h10 : (10 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have h12 : (12 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have hr7 : rho 7 = 10 := rho_spec.2.2.1
  have hr10 : rho 10 = 12 := rho_spec.2.2.2.1
  have hr12 : rho 12 = 7 := rho_spec.2.2.2.2
  have n2 : π 7 < π 10 ∧ π 7 < π 12 := hN.2.1
  have n2' : π' 7 < π' 10 ∧ π' 7 < π' 12 := hN'.2.1
  rw [hπ', Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hmO 7 h7, hmO 10 h10, hmO 12 h12] at n2'
  have hK : InK m := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simpa using hj
    · exfalso
      simp only [pow_one, hr7, hr10, hr12] at n2'
      exact absurd n2'.2 (not_lt.2 (le_of_lt n2.1))
    · exfalso
      simp only [pow_two, Perm.mul_apply, hr7, hr10, hr12] at n2'
      exact absurd n2'.1 (not_lt.2 (le_of_lt n2.2))
  -- `m = 1`, by (N3)
  have hq : m q1 = q1 := by
    have h3 := hN.2.2
    have h3' := hN'.2.2
    rw [hπ', map_O0_mul_InK hK.2, Perm.mul_apply] at h3'
    exact π.injective (h3'.unique h3)
  rw [hπ', InK_eq_one hK hq, mul_one]

/-- **Lemma 4.4.** For five distinct coordinates `c₁, …, c₅`, every Golay code `π₀(G24)` on the coordinates of `E`
is `π(G24)` for exactly one bijection `π` satisfying (N1)–(N3). -/
theorem lemma44 (c : Fin 5 → Fin 24) (hc : Function.Injective c) (π₀ : Perm (Fin 24)) :
    ∃! π : Perm (Fin 24),
      G24.map (permute π).toLinearMap = G24.map (permute π₀).toLinearMap ∧ NormalForm c π := by
  obtain ⟨π, hπ, hN⟩ := lemma44_exists c hc π₀
  refine ⟨π, ⟨map_permute_eq_iff.2 hπ, hN⟩, fun π' hπ'N => ?_⟩
  have h1 := map_permute_eq_iff.1 hπ'N.1
  have hm : π⁻¹ * π' ∈ Aut G24 := by
    have he : π⁻¹ * π' = (π₀⁻¹ * π)⁻¹ * (π₀⁻¹ * π') := by group
    rw [he]
    exact (Aut G24).mul_mem ((Aut G24).inv_mem hπ) h1
  exact (lemma44_unique hm hN hπ'N.2).symm

/-! ## Lemma 4.4 as the search uses it

The paper applies Lemma 4.4 as "each valid Golay code is found exactly once" (Sec. 4.3): validity depends only on the
code `π(G24)`, so the search may keep only bijections in normal form. -/

/-- An automorphism maps dodecads to dodecads. -/
theorem isDodecad_map {m : Perm (Fin 24)} (hm : m ∈ Aut G24) {D : Finset (Fin 24)} (hD : IsDodecad D) :
    IsDodecad (D.map m.toEmbedding) := by
  obtain ⟨x, hx, hx12, rfl⟩ := hD
  exact ⟨permute m x, permute_mem_of_mem_Aut hm hx, by rw [wt_permute, hx12], supp_permute m x⟩

/-- Validity depends only on the code `π(G24)`: `π m` with `m ∈ M₂₄` is valid exactly when `π` is. -/
theorem validGolay_mul_iff {E : Submodule F4 (Fin 24 → F4)} {π m : Perm (Fin 24)} (hm : m ∈ Aut G24) :
    ValidGolay E (π * m) ↔ ValidGolay E π := by
  have key : ∀ σ n : Perm (Fin 24), n ∈ Aut G24 → ValidGolay E σ → ValidGolay E (σ * n) := by
    intro σ n hn hv
    have himg : ∀ O : Finset (Fin 24),
        O.map (σ * n).toEmbedding = (O.map n.toEmbedding).map σ.toEmbedding :=
      fun O => by rw [Finset.map_map]; rfl
    refine ⟨fun O hO hf => hv.1 _ (isOctad_map hn hO) ?_, fun D hD hf => hv.2 _ (isDodecad_map hn hD) ?_⟩
    · rw [← himg]
      exact hf
    · rw [← himg]
      exact hf
  refine ⟨fun hv => ?_, key π m hm⟩
  have h := key (π * m) m⁻¹ ((Aut G24).inv_mem hm) hv
  rwa [mul_inv_cancel_right] at h

/-- **Lemma 4.4 as the search uses it**: a valid Golay code exists exactly when some `π(G24)` with `π` in normal
form for `c` is valid. -/
theorem exists_validGolay_iff_normalForm {E : Submodule F4 (Fin 24 → F4)} (c : Fin 5 → Fin 24)
    (hc : Function.Injective c) :
    (∃ π : Perm (Fin 24), ValidGolay E π) ↔ ∃ π : Perm (Fin 24), NormalForm c π ∧ ValidGolay E π := by
  constructor
  · rintro ⟨π₀, hv⟩
    obtain ⟨π, hπ, hN⟩ := lemma44_exists c hc π₀
    have h := (validGolay_mul_iff (E := E) (π := π₀) hπ).2 hv
    rw [mul_inv_cancel_left] at h
    exact ⟨π, hN, h⟩
  · rintro ⟨π, -, hv⟩
    exact ⟨π, hv⟩

end C72.Three.M24
