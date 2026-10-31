import C72T6O3.Lemma44

/-!
# T6 (order 3): Lemma 4.4 for an arbitrary configuration

The paper fixes an arbitrary octad `O₀` of `G24`, its points `p₁, …, p₈`, a point `q₁ ∉ O₀` and five coordinates
`c₁, …, c₅`. `C72T6O3.Lemma44` proves the lemma for the configuration of the point-placement program; here it is
transported to every configuration (`lemma44_general`): an octad `O'`, an enumeration `p'` of its points (any order;
the paper takes the increasing one) and a point `q' ∉ O'`. An element `m ∈ M₂₄` maps the program's configuration to
the given one (`exists_transport`: 5-transitivity, then a rotation in `H` and an element of `K`), and `π` is in normal
form for the given configuration exactly when `π m` is in normal form for the program's (`normalFormAt_iff`).
-/

namespace C72.Three.M24

open Equiv Finset

/-- (N1)–(N3) for the configuration `(O', p', q')`. -/
def NormalFormAt (O' : Finset (Fin 24)) (p' : Fin 8 → Fin 24) (q' : Fin 24) (c : Fin 5 → Fin 24)
    (π : Perm (Fin 24)) : Prop :=
  (∀ i : Fin 5, π (p' (Fin.castLE (by decide) i)) = c i) ∧ (π (p' 5) < π (p' 6) ∧ π (p' 5) < π (p' 7)) ∧
    IsLeast {y | y ∉ O'.map π.toEmbedding} (π q')

theorem normalFormAt_base (c : Fin 5 → Fin 24) (π : Perm (Fin 24)) :
    NormalFormAt O0 pp q1 c π ↔ NormalForm c π :=
  Iff.rfl

/-- Two octads sharing at least 5 points are equal. -/
theorem octad_eq_of_five {A B : Finset (Fin 24)} (hA : IsOctad A) (hB : IsOctad B) (h5 : 5 ≤ #(A ∩ B)) :
    A = B := by
  obtain ⟨x, hx, hx8, rfl⟩ := hA
  obtain ⟨y, hy, hy8, rfl⟩ := hB
  rw [eq_of_five hx hy hx8 hy8 h5]

/-- `π` is in normal form for `(O', p', q')` exactly when `π m` is in normal form for the program's configuration,
if `m` maps that configuration to `(O', p', q')`. -/
theorem normalFormAt_iff {O' : Finset (Fin 24)} {p' : Fin 8 → Fin 24} {q' : Fin 24} {m : Perm (Fin 24)}
    (h1 : ∀ i : Fin 5, m (bp i) = p' (Fin.castLE (by decide) i)) (h7 : m 7 = p' 5)
    (h1012 : (m 10 = p' 6 ∧ m 12 = p' 7) ∨ (m 10 = p' 7 ∧ m 12 = p' 6)) (hq : m q1 = q')
    (hO : O0.map m.toEmbedding = O') (c : Fin 5 → Fin 24) (π : Perm (Fin 24)) :
    NormalFormAt O' p' q' c π ↔ NormalForm c (π * m) := by
  have himg : O0.map (π * m).toEmbedding = O'.map π.toEmbedding := by
    rw [← hO, Finset.map_map]
    rfl
  have hN1 : (∀ i : Fin 5, π (p' (Fin.castLE (by decide) i)) = c i) ↔ ∀ i : Fin 5, (π * m) (bp i) = c i := by
    refine forall_congr' fun i => ?_
    rw [Perm.mul_apply, h1]
  have hN2 : (π (p' 5) < π (p' 6) ∧ π (p' 5) < π (p' 7)) ↔
      ((π * m) (pp 5) < (π * m) (pp 6) ∧ (π * m) (pp 5) < (π * m) (pp 7)) := by
    show _ ↔ ((π * m) 7 < (π * m) 10 ∧ (π * m) 7 < (π * m) 12)
    rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, h7]
    rcases h1012 with ⟨h10, h12⟩ | ⟨h10, h12⟩
    · rw [h10, h12]
    · rw [h10, h12, and_comm]
  have hN3 : IsLeast {y | y ∉ O'.map π.toEmbedding} (π q') ↔
      IsLeast {y | y ∉ O0.map (π * m).toEmbedding} ((π * m) q1) := by
    rw [himg, Perm.mul_apply, hq]
  exact and_congr hN1 (and_congr hN2 hN3)

/-- An element of `M₂₄` maps the program's configuration `(O₀, p, q₁)` to any configuration `(O', p', q')`. -/
theorem exists_transport {O' : Finset (Fin 24)} (hO' : IsOctad O') {p' : Fin 8 → Fin 24}
    (hp' : Function.Injective p') (hpO : ∀ i, p' i ∈ O') {q' : Fin 24} (hq' : q' ∉ O') :
    ∃ m ∈ Aut G24, (∀ i : Fin 5, m (bp i) = p' (Fin.castLE (by decide) i)) ∧ m 7 = p' 5 ∧
      ((m 10 = p' 6 ∧ m 12 = p' 7) ∨ (m 10 = p' 7 ∧ m 12 = p' 6)) ∧ m q1 = q' ∧ O0.map m.toEmbedding = O' := by
  -- `O'` is the image of `p'`
  have hcard : #O' = 8 := by
    obtain ⟨x, _, hx8, rfl⟩ := hO'
    rw [card_supp, hx8]
  have himgp : (Finset.univ.map ⟨p', hp'⟩) = O' := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact hpO i
    · rw [hcard, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hsurj : ∀ y ∈ O', ∃ i, p' i = y := fun y hy => by
    rw [← himgp, Finset.mem_map] at hy
    obtain ⟨i, _, hi⟩ := hy
    exact ⟨i, hi⟩
  -- 5-transitivity
  obtain ⟨m0, hm0, hm0i⟩ := five_transitive (fun i => p' (Fin.castLE (by decide) i))
    (fun i j hij => Fin.castLE_injective _ (hp' hij))
  have hO0 : O0.map m0.toEmbedding = O' := by
    refine octad_eq_of_five (isOctad_map hm0 O0_isOctad) hO' ?_
    have hsub : (Finset.univ : Finset (Fin 5)).map ⟨fun i => p' (Fin.castLE (by decide) i),
        fun i j hij => Fin.castLE_injective _ (hp' hij)⟩ ⊆ O0.map m0.toEmbedding ∩ O' := by
      intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨i, _, rfl⟩ := hy
      refine Finset.mem_inter.2 ⟨?_, hpO _⟩
      rw [Finset.mem_map]
      exact ⟨bp i, bp_mem_O0 i, hm0i i⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
    exact this
  -- `m0` maps `{7, 10, 12}` onto `{p'₆, p'₇, p'₈}`
  have hmem : ∀ y ∈ O0, ∃ i, m0 y = p' i := fun y hy => by
    obtain ⟨i, hi⟩ := hsurj (m0 y) (by rw [← hO0, Finset.mem_map]; exact ⟨y, hy, rfl⟩)
    exact ⟨i, hi.symm⟩
  have h7 : (7 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have h10 : (10 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have h12 : (12 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have hnot : ∀ (y : Fin 24), y = 7 ∨ y = 10 ∨ y = 12 → ∀ j : Fin 5, m0 y ≠ p' (Fin.castLE (by decide) j) :=
    fun y hy j hj => by
      rw [← hm0i j] at hj
      have hyj := m0.injective hj
      have hne : ∀ y : Fin 24, y = 7 ∨ y = 10 ∨ y = 12 → ∀ j : Fin 5, y ≠ bp j := by decide
      exact hne y hy j hyj
  have hhigh : ∀ (y : Fin 24), y = 7 ∨ y = 10 ∨ y = 12 → m0 y = p' 5 ∨ m0 y = p' 6 ∨ m0 y = p' 7 :=
    fun y hy => by
      have hyO : y ∈ O0 := by rcases hy with rfl | rfl | rfl <;> assumption
      obtain ⟨i, hi⟩ := hmem y hyO
      have hi5 : ∀ j : Fin 5, i ≠ Fin.castLE (by decide) j := fun j hij => hnot y hy j (by rw [hi, hij])
      have hcl : ∀ i : Fin 8, (∀ j : Fin 5, i ≠ Fin.castLE (by decide) j) → i = 5 ∨ i = 6 ∨ i = 7 := by decide
      rcases hcl i hi5 with rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
  have hd1 : m0 7 ≠ m0 10 := fun h => absurd (m0.injective h) (by decide)
  have hd2 : m0 7 ≠ m0 12 := fun h => absurd (m0.injective h) (by decide)
  have hd3 : m0 10 ≠ m0 12 := fun h => absurd (m0.injective h) (by decide)
  have hp56 : p' 5 ≠ p' 6 := fun h => absurd (hp' h) (by decide)
  have hp57 : p' 5 ≠ p' 7 := fun h => absurd (hp' h) (by decide)
  have hp67 : p' 6 ≠ p' 7 := fun h => absurd (hp' h) (by decide)
  have hr7 : rho 7 = 10 := rho_spec.2.2.1
  have hr10 : rho 10 = 12 := rho_spec.2.2.2.1
  have hr12 : rho 12 = 7 := rho_spec.2.2.2.2
  -- a rotation `ρʳ` makes `p₆ ↦ p'₆`
  obtain ⟨r, hr, h1', h7', h1012'⟩ : ∃ r : ℕ, InH (rho ^ r) ∧
      (∀ i : Fin 5, (m0 * rho ^ r) (bp i) = p' (Fin.castLE (by decide) i)) ∧ (m0 * rho ^ r) 7 = p' 5 ∧
      (((m0 * rho ^ r) 10 = p' 6 ∧ (m0 * rho ^ r) 12 = p' 7) ∨
        ((m0 * rho ^ r) 10 = p' 7 ∧ (m0 * rho ^ r) 12 = p' 6)) := by
    have hfix : ∀ r : ℕ, ∀ i : Fin 5, (m0 * rho ^ r) (bp i) = p' (Fin.castLE (by decide) i) := fun r i => by
      rw [Perm.mul_apply, (rho_InH.pow r).2 i, hm0i]
    have a7 := hhigh 7 (Or.inl rfl)
    have a10 := hhigh 10 (Or.inr (Or.inl rfl))
    have a12 := hhigh 12 (Or.inr (Or.inr rfl))
    rcases a7 with e7 | e7 | e7
    · refine ⟨0, rho_InH.pow 0, hfix 0, by simpa using e7, ?_⟩
      simp only [pow_zero, mul_one]
      rcases a10 with e10 | e10 | e10
      · exact absurd (e7.trans e10.symm) hd1
      · rcases a12 with e12 | e12 | e12
        · exact absurd (e7.trans e12.symm) hd2
        · exact absurd (e10.trans e12.symm) hd3
        · exact Or.inl ⟨e10, e12⟩
      · rcases a12 with e12 | e12 | e12
        · exact absurd (e7.trans e12.symm) hd2
        · exact Or.inr ⟨e10, e12⟩
        · exact absurd (e10.trans e12.symm) hd3
    · -- `m0 7 = p'₆`: the point mapped to `p'₅` is 10 or 12
      rcases a10 with e10 | e10 | e10
      · -- `m0 10 = p'₅`: take `ρ` (`7 ↦ 10`)
        refine ⟨1, rho_InH.pow 1, hfix 1, by rw [Perm.mul_apply, pow_one, hr7, e10], ?_⟩
        rw [Perm.mul_apply, Perm.mul_apply, pow_one, hr10, hr12, e7]
        rcases a12 with e12 | e12 | e12
        · exact absurd (e10.trans e12.symm) hd3
        · exact absurd (e7.trans e12.symm) hd2
        · exact Or.inr ⟨e12, rfl⟩
      · exact absurd (e7.trans e10.symm) hd1
      · -- `m0 12 = p'₅`: take `ρ²` (`7 ↦ 12`)
        rcases a12 with e12 | e12 | e12
        · refine ⟨2, rho_InH.pow 2, hfix 2, by rw [Perm.mul_apply, pow_two, Perm.mul_apply, hr7, hr10, e12], ?_⟩
          rw [Perm.mul_apply, Perm.mul_apply, pow_two, Perm.mul_apply, Perm.mul_apply, hr10, hr12, hr7, e7, e10]
          exact Or.inl ⟨rfl, rfl⟩
        · exact absurd (e7.trans e12.symm) hd2
        · exact absurd (e10.trans e12.symm) hd3
    · -- `m0 7 = p'₇`
      rcases a10 with e10 | e10 | e10
      · refine ⟨1, rho_InH.pow 1, hfix 1, by rw [Perm.mul_apply, pow_one, hr7, e10], ?_⟩
        rw [Perm.mul_apply, Perm.mul_apply, pow_one, hr10, hr12, e7]
        rcases a12 with e12 | e12 | e12
        · exact absurd (e10.trans e12.symm) hd3
        · exact Or.inl ⟨e12, rfl⟩
        · exact absurd (e7.trans e12.symm) hd2
      · rcases a12 with e12 | e12 | e12
        · refine ⟨2, rho_InH.pow 2, hfix 2, by rw [Perm.mul_apply, pow_two, Perm.mul_apply, hr7, hr10, e12], ?_⟩
          rw [Perm.mul_apply, Perm.mul_apply, pow_two, Perm.mul_apply, Perm.mul_apply, hr10, hr12, hr7, e7, e10]
          exact Or.inr ⟨rfl, rfl⟩
        · exact absurd (e10.trans e12.symm) hd3
        · exact absurd (e7.trans e12.symm) hd2
      · exact absurd (e7.trans e10.symm) hd1
  obtain ⟨m1, hm1def⟩ : ∃ m1, m1 = m0 * rho ^ r := ⟨_, rfl⟩
  rw [← hm1def] at h1' h7' h1012'
  have hm1 : m1 ∈ Aut G24 := by
    rw [hm1def]
    exact (Aut G24).mul_mem hm0 hr.1
  have hO1 : O0.map m1.toEmbedding = O' := by rw [hm1def, map_O0_mul_InH hr, hO0]
  -- an element of `K` makes `q₁ ↦ q'`
  have hx : m1.symm q' ∉ O0 := by
    intro hxO
    apply hq'
    rw [← hO1, Finset.mem_map]
    exact ⟨_, hxO, by simp⟩
  obtain ⟨hk, hkfix, hkq⟩ := kq_spec _ hx
  refine ⟨m1 * kq (m1.symm q'), (Aut G24).mul_mem hm1 hk, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mul_apply, hkfix _ (bp_mem_O0 i), h1']
  · rw [Perm.mul_apply, hkfix 7 h7, h7']
  · rw [Perm.mul_apply m1 _ 10, Perm.mul_apply m1 _ 12, hkfix 10 h10, hkfix 12 h12]
    exact h1012'
  · rw [Perm.mul_apply, hkq, Equiv.apply_symm_apply]
  · rw [map_O0_mul_InK hkfix, hO1]

/-- **Lemma 4.4** for any configuration: an octad `O'` of `G24`, an enumeration `p'` of its points, a point
`q' ∉ O'` and five distinct coordinates `c`. Every Golay code `π₀(G24)` is `π(G24)` for exactly one `π` in normal
form for `(O', p', q')`. -/
theorem lemma44_general {O' : Finset (Fin 24)} (hO' : IsOctad O') {p' : Fin 8 → Fin 24}
    (hp' : Function.Injective p') (hpO : ∀ i, p' i ∈ O') {q' : Fin 24} (hq' : q' ∉ O')
    (c : Fin 5 → Fin 24) (hc : Function.Injective c) (π₀ : Perm (Fin 24)) :
    ∃! π : Perm (Fin 24),
      G24.map (permute π).toLinearMap = G24.map (permute π₀).toLinearMap ∧ NormalFormAt O' p' q' c π := by
  obtain ⟨m, hm, h1, h7, h1012, hq, hO⟩ := exists_transport hO' hp' hpO hq'
  have hiff := normalFormAt_iff h1 h7 h1012 hq hO c
  have hsame : ∀ π : Perm (Fin 24), G24.map (permute (π * m)).toLinearMap = G24.map (permute π).toLinearMap :=
    fun π => map_permute_eq_iff.2 (by rw [← mul_assoc, inv_mul_cancel, one_mul]; exact hm)
  obtain ⟨σ, ⟨hσ, hσN⟩, hσu⟩ := lemma44 c hc (π₀ * m)
  refine ⟨σ * m⁻¹, ⟨?_, ?_⟩, fun π' ⟨h', hN'⟩ => ?_⟩
  · rw [← hsame (σ * m⁻¹), inv_mul_cancel_right, hσ, hsame]
  · rw [hiff, inv_mul_cancel_right]
    exact hσN
  · have h2 := hσu (π' * m) ⟨by rw [hsame, h', hsame], (hiff π').1 hN'⟩
    rw [← h2, mul_inv_cancel_right]

end C72.Three.M24
