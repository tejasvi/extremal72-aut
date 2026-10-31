import C72T6O3.M24Data
import C72T6O3.Closure

/-!
# T6 (order 3): the facts on `M₂₄ = Aut G24` used by Lemma 4.4, certified by data and Bool checks

The base configuration is the one of the point-placement program (`csp5p.c`): `O₀` is the first octad of
`octdod.txt` (mask 5279, `O₀ = {0, 1, 2, 3, 4, 7, 10, 12}`, `O0_eq`), `p₁ < ⋯ < p₈` are its points (`pp`) and
`q₁ = 5` is the smallest point outside `O₀` (`q1_spec`). `H` is the pointwise stabiliser of `p₁, …, p₅` in
`Aut G24` and `K` the pointwise stabiliser of `O₀` (`InH`, `InK`).

* 5-transitivity from the base `p₁, …, p₅` (`five_transitive`): stabiliser-chain transversals `trans k x`, each
  checked to lie in `Aut G24`, to fix `p₁, …, p_k` and to map `p_{k+1}` to `x` (`transOK_eq`, one kernel check over
  the 110 elements).
* `H` fixes `O₀` setwise (`map_O0_of_InH`, since `O₀` is the only octad through `p₁, …, p₅`) and acts on
  `{p₆, p₇, p₈}` by the three rotations: `rho ∈ H` induces `p₆ ↦ p₇ ↦ p₈ ↦ p₆` (`rho_spec`) and every `h ∈ H` is
  `ρʲ k` with `k ∈ K` (`InH_eq_rho_pow_mul`).
* `K` acts regularly on the 16 points outside `O₀`: `kq x ∈ K` maps `q₁` to `x` (`kq_spec`), and an element of `K`
  fixing `q₁` is the identity (`InK_eq_one`, from the closure certificate `eq_one_of_fixes`).
-/

namespace C72.Three.M24

open Equiv Finset

/-! ## The base configuration -/

/-- `O₀`: the first octad of `octdod.txt`, mask 5279. -/
def O0 : Finset (Fin 24) :=
  supp (toVec 5279)

theorem O0_eq : O0 = {0, 1, 2, 3, 4, 7, 10, 12} := by
  ext y
  revert y
  decide

theorem O0_isOctad : IsOctad O0 :=
  isOctad_iff.2 ⟨5279, by decide, rfl⟩

/-- `p₁ < ⋯ < p₈`: the points of `O₀` in increasing order. -/
def pp : Fin 8 → Fin 24 :=
  ![0, 1, 2, 3, 4, 7, 10, 12]

/-- `q₁`: the smallest point outside `O₀`. -/
def q1 : Fin 24 :=
  5

theorem pp_spec : (∀ i, pp i ∈ O0) ∧ ∀ i j : Fin 8, i < j → pp i < pp j := by
  decide

theorem q1_spec : q1 ∉ O0 ∧ ∀ y : Fin 24, y < q1 → y ∈ O0 := by
  decide

/-- The base points `p₁, …, p₅`. -/
def bp (j : Fin 5) : Fin 24 :=
  pp (Fin.castLE (by decide) j)

theorem bp_val : ∀ j : Fin 5, (bp j).val = j.val := by
  decide

theorem bp_mem_O0 (j : Fin 5) : bp j ∈ O0 :=
  pp_spec.1 _

/-! ## 5-transitivity -/

/-- Bool check of the transversals: `trans k x ∈ Aut G24`, it fixes `p₁, …, p_k` and maps `p_{k+1}` to `x`, for
every `k < 5` and every `x` outside `{p₁, …, p_k}` (that is, `k ≤ x`). -/
def transOK : Bool :=
  (List.finRange 5).all fun k => (List.finRange 24).all fun x =>
    !decide (k.val ≤ x.val) ||
      (autOK (trans k x) &&
        ((List.finRange 5).all fun j => !decide (j < k) || decide (trans k x (bp j) = bp j)) &&
        decide (trans k x (bp k) = x))

/-- **The kernel check of the 110 transversal elements.** -/
theorem transOK_eq : transOK = true := by
  decide +kernel

theorem trans_spec (k : Fin 5) (x : Fin 24) (hx : k.val ≤ x.val) :
    trans k x ∈ Aut G24 ∧ (∀ j : Fin 5, j < k → trans k x (bp j) = bp j) ∧ trans k x (bp k) = x := by
  have h := transOK_eq
  simp only [transOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h k x with h1 | ⟨⟨h2, h3⟩, h4⟩
  · exact absurd hx h1
  · refine ⟨mem_Aut_of_autOK h2, fun j hj => ?_, h4⟩
    rcases h3 j with h5 | h5
    · exact absurd hj h5
    · exact h5

/-- **5-transitivity** (from the base `p₁, …, p₅`): for any five distinct points `a₁, …, a₅` there is
`m ∈ Aut G24` with `m(pᵢ) = aᵢ`. -/
theorem five_transitive (a : Fin 5 → Fin 24) (ha : Function.Injective a) :
    ∃ m ∈ Aut G24, ∀ i : Fin 5, m (bp i) = a i := by
  suffices H : ∀ n : ℕ, n ≤ 5 → ∃ m ∈ Aut G24, ∀ i : Fin 5, i.val < n → m (bp i) = a i by
    obtain ⟨m, hm, hmi⟩ := H 5 le_rfl
    exact ⟨m, hm, fun i => hmi i i.isLt⟩
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨1, (Aut G24).one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨m, hm, hmi⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k : Fin 5, k.val = n := ⟨⟨n, by omega⟩, rfl⟩
    have hx : k.val ≤ (m.symm (a k)).val := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨j, hj⟩ : ∃ j : Fin 5, j.val = (m.symm (a k)).val :=
        ⟨⟨(m.symm (a k)).val, by have := k.isLt; omega⟩, rfl⟩
      have hbj : bp j = m.symm (a k) := Fin.ext (by rw [bp_val, hj])
      have hmj := hmi j (by omega)
      rw [hbj, Equiv.apply_symm_apply] at hmj
      have hjk : j = k := ha hmj.symm
      rw [hjk] at hj
      omega
    obtain ⟨hu, hfix, hmap⟩ := trans_spec k (m.symm (a k)) hx
    refine ⟨m * trans k (m.symm (a k)), (Aut G24).mul_mem hm hu, fun i hi => ?_⟩
    rw [Perm.mul_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · rw [hfix i (Fin.lt_def.2 (by omega))]
      exact hmi i hlt
    · have hik : i = k := Fin.ext (by omega)
      rw [hik, hmap, Equiv.apply_symm_apply]

/-! ## The rotation and the group `K` -/

theorem rho_spec : rho ∈ Aut G24 ∧ (∀ j : Fin 5, rho (bp j) = bp j) ∧ rho 7 = 10 ∧ rho 10 = 12 ∧
    rho 12 = 7 := by
  refine ⟨mem_Aut_of_autOK (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- Bool check of `kq`: for `x ∉ O₀`, `kq x ∈ Aut G24`, it fixes `O₀` pointwise and maps `q₁` to `x`. -/
def kqOK : Bool :=
  (List.finRange 24).all fun x =>
    decide (x ∈ O0) ||
      (autOK (kq x) && ((List.finRange 24).all fun y => !decide (y ∈ O0) || decide (kq x y = y)) &&
        decide (kq x q1 = x))

/-- **The kernel check of the 16 elements of `K`.** -/
theorem kqOK_eq : kqOK = true := by
  decide +kernel

theorem kq_spec (x : Fin 24) (hx : x ∉ O0) : kq x ∈ Aut G24 ∧ (∀ y ∈ O0, kq x y = y) ∧ kq x q1 = x := by
  have h := kqOK_eq
  simp only [kqOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h x with h1 | ⟨⟨h2, h3⟩, h4⟩
  · exact absurd h1 hx
  · refine ⟨mem_Aut_of_autOK h2, fun y hy => ?_, h4⟩
    rcases h3 y with h5 | h5
    · exact absurd hy h5
    · exact h5

/-! ## `H` and `K` -/

/-- `h ∈ H`: an automorphism of `G24` fixing `p₁, …, p₅`. -/
def InH (h : Perm (Fin 24)) : Prop :=
  h ∈ Aut G24 ∧ ∀ j : Fin 5, h (bp j) = bp j

/-- `k ∈ K`: an automorphism of `G24` fixing `O₀` pointwise. -/
def InK (k : Perm (Fin 24)) : Prop :=
  k ∈ Aut G24 ∧ ∀ y ∈ O0, k y = y

variable {h k : Perm (Fin 24)}

theorem InK.InH (hk : InK k) : InH k :=
  ⟨hk.1, fun j => hk.2 _ (bp_mem_O0 j)⟩

theorem rho_InH : InH rho :=
  ⟨rho_spec.1, rho_spec.2.1⟩

theorem InH.mul {h h' : Perm (Fin 24)} (hh : InH h) (hh' : InH h') : InH (h * h') :=
  ⟨(Aut G24).mul_mem hh.1 hh'.1, fun j => by rw [Perm.mul_apply, hh'.2, hh.2]⟩

theorem InH.inv (hh : InH h) : InH h⁻¹ :=
  ⟨(Aut G24).inv_mem hh.1, fun j => by
    have := hh.2 j
    rw [Perm.inv_eq_iff_eq]
    exact this.symm⟩

theorem InH.pow (hh : InH h) : ∀ n : ℕ, InH (h ^ n)
  | 0 => ⟨(Aut G24).one_mem, fun _ => rfl⟩
  | n + 1 => by
    rw [pow_succ]
    exact (InH.pow hh n).mul hh

/-- `H` maps `O₀` onto itself: `O₀` is the only octad through `p₁, …, p₅`. -/
theorem map_O0_of_InH (hh : InH h) : O0.map h.toEmbedding = O0 := by
  refine map_octad_eq hh.1 O0_isOctad (S := (Finset.univ : Finset (Fin 5)).map ⟨bp, ?_⟩) ?_ ?_ ?_
  · intro i j hij
    exact Fin.ext (by have := congrArg Fin.val hij; rwa [bp_val, bp_val] at this)
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨j, _, rfl⟩ := hy
    exact bp_mem_O0 j
  · simp
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨j, _, rfl⟩ := hy
    exact hh.2 j

/-- An element of `H` maps the complement of `O₀` to itself. -/
theorem InH.apply_not_mem (hh : InH h) {y : Fin 24} (hy : y ∉ O0) : h y ∉ O0 := by
  intro hhy
  rw [← map_O0_of_InH hh, Finset.mem_map] at hhy
  obtain ⟨w, hw, hwy⟩ := hhy
  have hwy' : w = y := h.injective (by simpa using hwy)
  rw [hwy'] at hw
  exact hy hw

/-- An element of `H` maps `O₀` to itself. -/
theorem InH.apply_mem (hh : InH h) {y : Fin 24} (hy : y ∈ O0) : h y ∈ O0 := by
  rw [← map_O0_of_InH hh, Finset.mem_map]
  exact ⟨y, hy, rfl⟩

/-- An element of `H` fixing `p₆` is in `K`. -/
theorem InK_of_InH (hh : InH h) (h7 : h 7 = 7) : InK h := by
  have hx : h q1 ∉ O0 := hh.apply_not_mem q1_spec.1
  obtain ⟨hk, hkfix, hkq⟩ := kq_spec (h q1) hx
  have hkinv : ∀ y ∈ O0, (kq (h q1))⁻¹ y = y := fun y hy => by
    rw [Perm.inv_eq_iff_eq]
    exact (hkfix y hy).symm
  have h1 : (kq (h q1))⁻¹ * h = 1 := by
    apply eq_one_of_fixes ((Aut G24).mul_mem ((Aut G24).inv_mem hk) hh.1)
    intro y hy
    rw [Perm.mul_apply]
    have hO := O0_eq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (0 : Fin 24) = bp 0 from rfl, hh.2, hkinv _ (bp_mem_O0 0)]
    · rw [show (1 : Fin 24) = bp 1 from rfl, hh.2, hkinv _ (bp_mem_O0 1)]
    · rw [show (2 : Fin 24) = bp 2 from rfl, hh.2, hkinv _ (bp_mem_O0 2)]
    · rw [show (3 : Fin 24) = bp 3 from rfl, hh.2, hkinv _ (bp_mem_O0 3)]
    · rw [show (4 : Fin 24) = bp 4 from rfl, hh.2, hkinv _ (bp_mem_O0 4)]
    · rw [h7, hkinv _ (by rw [hO]; decide)]
    · show (kq (h q1))⁻¹ (h q1) = q1
      rw [Perm.inv_eq_iff_eq, hkq]
  have heq : h = kq (h q1) := by
    calc h = kq (h q1) * ((kq (h q1))⁻¹ * h) := by group
      _ = kq (h q1) := by rw [h1, mul_one]
  rw [heq]
  exact ⟨hk, hkfix⟩

/-- **`H` acts on `{p₆, p₇, p₈}` by rotations**: every `h ∈ H` is `ρʲ k` with `j < 3` and `k ∈ K`. -/
theorem InH_eq_rho_pow_mul (hh : InH h) : ∃ j : ℕ, j < 3 ∧ InK ((rho ^ j)⁻¹ * h) := by
  have h7mem : h 7 ∈ O0 := hh.apply_mem (by rw [O0_eq]; decide)
  have hne : ∀ j : Fin 5, (7 : Fin 24) ≠ bp j := by
    decide
  have h7ne : ∀ j : Fin 5, h 7 ≠ bp j := fun j hj => by
    rw [← hh.2 j] at hj
    exact hne j (h.injective hj)
  have hcl : ∀ y : Fin 24, y ∈ O0 → (∀ j : Fin 5, y ≠ bp j) → y = 7 ∨ y = 10 ∨ y = 12 := by
    decide
  have hr7 : rho 7 = 10 := rho_spec.2.2.1
  have hr10 : rho 10 = 12 := rho_spec.2.2.2.1
  rcases hcl (h 7) h7mem h7ne with h' | h' | h'
  · refine ⟨0, by norm_num, ?_⟩
    simp only [pow_zero, inv_one, one_mul]
    exact InK_of_InH hh h'
  · refine ⟨1, by norm_num, ?_⟩
    rw [pow_one]
    refine InK_of_InH (rho_InH.inv.mul hh) ?_
    rw [Perm.mul_apply, h', Perm.inv_eq_iff_eq, hr7]
  · refine ⟨2, by norm_num, ?_⟩
    refine InK_of_InH ((rho_InH.pow 2).inv.mul hh) ?_
    rw [Perm.mul_apply, h', Perm.inv_eq_iff_eq, pow_two, Perm.mul_apply, hr7, hr10]

/-- **`K` acts freely on the complement of `O₀`**: an element of `K` fixing `q₁` is the identity. -/
theorem InK_eq_one (hk : InK k) (hq : k q1 = q1) : k = 1 := by
  apply eq_one_of_fixes hk.1
  intro y hy
  have hO := O0_eq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hq
    | exact hk.2 _ (by rw [hO]; decide)

end C72.Three.M24
