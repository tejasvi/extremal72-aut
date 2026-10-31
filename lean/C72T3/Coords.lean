import C72T3.MDef
import C72T1.Labelling
import C72T1.Decomp

/-!
# T3: the coordinates of Sec. 2.1, the maps `φ₀` and `φ₁`

After relabelling (`C72T1.Labelling`), the automorphism of order 5 is `g5 = stdPerm 14 5 2`: the `a`-th cycle
is `{5a, …, 5a+4}`, on which `g5` acts as `5a + b ↦ 5a + (b + 1 mod 5)`, and 70, 71 are fixed. The structured
coordinates `Z = (Fin 14 × Fin 5) ⊕ Fin 2` are numbered by `E72` (`(a, b) ↦ 5a + b`, `inr x ↦ 70 + x`).

* `phi0 u` repeats `u a` on the `a`-th cycle and puts `u (14 + x)` on the fixed point `70 + x`
  (`u : 𝔽₂¹⁶`, the paper's `(a, x)`). Its image is exactly the set of words fixed by `g5`
  (`phi0_fixed`, `exists_phi0_eq`), and `⟨φ₀u, φ₀u'⟩ = ⟨u, u'⟩` (`phi0_dot`).
* `phi1 c` applies `ψ` on each cycle (`c ∈ 𝔽₁₆¹⁴`) and is `0` on the fixed points. It is additive and
  injective, `g5` acts as multiplication by `t` (`permute_g5_phi1`), `⟨φ₁c, φ₁c'⟩ = Tr⟨c, c'⟩` (`phi1_dot`), and
  `φ₁c ⊥ φ₀u` (`phi1_dot_phi0`).
* The weight of `φ₀u + φ₁c` is computed cycle by cycle (`wt_phi0_add_phi1`).
-/

namespace C72.T3

open Equiv Equiv.Perm Finset

/-- The structured coordinates of Sec. 2.1: `inl (a, b)` is the `b`-th coordinate of the `a`-th cycle,
`inr x` is the `x`-th fixed point. -/
abbrev Z := (Fin 14 × Fin 5) ⊕ Fin 2

/-- The numbering of Sec. 2.1 (`blockEquiv` of `C72T1.Labelling`): `(a, b) ↦ 5a + b`, `inr x ↦ 70 + x`. -/
def E72 : Z ≃ Fin 72 :=
  (blockEquiv 14 5 2).trans (finCongr rfl)

theorem E72_val : ∀ z : Z, (E72 z).val = (match z with
    | Sum.inl (a, b) => 5 * a.val + b.val
    | Sum.inr x => 70 + x.val) := by
  decide +kernel

/-- The automorphism of order 5 in the numbering of Sec. 2.1. -/
def g5 : Perm (Fin 72) :=
  stdPerm 14 5 2 rfl

theorem g5_eq : g5 = E72.permCongr (stdShift 14 5 2) :=
  rfl

theorem g5_E72 (z : Z) : g5 (E72 z) = E72 (stdShift 14 5 2 z) := by
  rw [g5_eq, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem g5_symm_E72 (z : Z) : g5.symm (E72 z) = E72 ((stdShift 14 5 2).symm z) := by
  rw [Equiv.symm_apply_eq, g5_E72, Equiv.apply_symm_apply]

theorem g5_pow_E72 (k : ℕ) (z : Z) : (g5 ^ k) (E72 z) = E72 ((stdShift 14 5 2 ^ k) z) := by
  rw [g5_eq, C72.permCongr_pow, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem stdShift_symm_inl (a : Fin 14) (b : Fin 5) :
    (stdShift 14 5 2).symm (Sum.inl (a, b)) = Sum.inl (a, (finRotate 5).symm b) :=
  rfl

theorem stdShift_symm_inr (x : Fin 2) : (stdShift 14 5 2).symm (Sum.inr x) = Sum.inr x :=
  rfl

theorem g5_pow_five : g5 ^ 5 = 1 := by
  rw [g5_eq, C72.permCongr_pow, stdShift_pow_prime (by norm_num : Nat.Prime 5)]
  ext x
  simp

theorem orderOf_g5 : orderOf g5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime g5_pow_five
  intro h
  have h0 : g5 0 = 1 := Tests.stdPerm_14_5_2.1
  rw [h] at h0
  exact absurd h0 (by decide)

theorem finRotate_pow_zero_apply : ∀ b : Fin 5, (finRotate 5 ^ b.val) 0 = b := by decide +kernel

/-! ## `φ₀` -/

/-- The cycle or fixed point of a coordinate, numbered as the coordinates of `C₀ ≤ 𝔽₂¹⁶`: the cycle `a` is `a`,
the fixed point `x` is `14 + x`. -/
def orb : Z → Fin 16
  | Sum.inl (a, _) => Fin.castAdd 2 a
  | Sum.inr x => Fin.natAdd 14 x

/-- `φ₀`: repeats `u a` on the `a`-th cycle and puts `u (14 + x)` on the fixed point `70 + x` (Sec. 2.1). -/
def phi0 : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 72 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i => orb (E72.symm i))

theorem phi0_E72 (u : Fin 16 → ZMod 2) (z : Z) : phi0 u (E72 z) = u (orb z) := by
  simp [phi0, LinearMap.funLeft_apply]

/-- `φ₀u` is fixed by `g5`. -/
theorem phi0_fixed (u : Fin 16 → ZMod 2) (i : Fin 72) : phi0 u (g5 i) = phi0 u i := by
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [g5_E72, phi0_E72, phi0_E72]
  rcases z with ⟨a, b⟩ | x <;> rfl

theorem permute_g5_phi0 (u : Fin 16 → ZMod 2) : permute g5 (phi0 u) = phi0 u :=
  (permute_eq_self_iff g5).2 (phi0_fixed u)

/-- Every word fixed by `g5` is `φ₀u`. -/
theorem exists_phi0_eq {v : Fin 72 → ZMod 2} (hv : ∀ i, v (g5 i) = v i) : ∃ u, phi0 u = v := by
  refine ⟨fun j => Fin.addCases (fun a => v (E72 (Sum.inl (a, 0)))) (fun x => v (E72 (Sum.inr x))) j, ?_⟩
  funext i
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [phi0_E72]
  rcases z with ⟨a, b⟩ | x
  · simp only [orb, Fin.addCases_left]
    have h := apply_pow_of_fixed g5 hv b.val (E72 (Sum.inl (a, 0)))
    rw [g5_pow_E72, stdShift_pow_inl, finRotate_pow_zero_apply] at h
    exact h.symm
  · simp only [orb, Fin.addCases_right]

theorem zmod2_five_smul : ∀ y : ZMod 2, (5 : ℕ) • y = y := by decide

theorem sum_fin16 {M : Type*} [AddCommMonoid M] (f : Fin 16 → M) :
    ∑ i, f i = ∑ a : Fin 14, f (Fin.castAdd 2 a) + ∑ x : Fin 2, f (Fin.natAdd 14 x) :=
  Fin.sum_univ_add (a := 14) (b := 2) f

theorem tr_sum {ι : Type*} [Fintype ι] (f : ι → F16) : tr (∑ i, f i) = ∑ i, tr (f i) :=
  map_sum trHom f univ

/-- `⟨φ₀u, φ₀u'⟩ = ⟨u, u'⟩`: every cycle has odd length. -/
theorem phi0_dot (u u' : Fin 16 → ZMod 2) : phi0 u ⬝ᵥ phi0 u' = u ⬝ᵥ u' := by
  simp only [dotProduct]
  rw [← Equiv.sum_comp E72, Fintype.sum_sum_type, Fintype.sum_prod_type, sum_fin16]
  simp only [phi0_E72, orb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, zmod2_five_smul]

/-- `φ₀` is injective. -/
theorem phi0_injective : Function.Injective phi0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  funext j
  have h := phi0_dot u (Pi.single j 1)
  rw [hu, zero_dotProduct, dotProduct_single, mul_one] at h
  exact h.symm

/-! ## `φ₁` -/

/-- `φ₁` on structured coordinates: `ψ(c a)` on the `a`-th cycle, `0` on the fixed points. -/
def phi1Z (c : Fin 14 → F16) : Z → ZMod 2
  | Sum.inl (a, b) => psi (c a) b
  | Sum.inr _ => 0

/-- `φ₁` (Sec. 2.1): applies `ψ` on each cycle, `0` on the fixed points. -/
def phi1 : (Fin 14 → F16) →+ (Fin 72 → ZMod 2) where
  toFun c i := phi1Z c (E72.symm i)
  map_zero' := by
    funext i
    generalize E72.symm i = z
    rcases z with ⟨a, b⟩ | x
    · simp [phi1Z, psi_zero]
    · rfl
  map_add' c c' := by
    funext i
    show phi1Z (c + c') (E72.symm i) = phi1Z c (E72.symm i) + phi1Z c' (E72.symm i)
    generalize E72.symm i = z
    rcases z with ⟨a, b⟩ | x
    · simp [phi1Z, psi_add]
    · simp [phi1Z]

theorem phi1_E72 (c : Fin 14 → F16) (z : Z) : phi1 c (E72 z) = phi1Z c z := by
  simp [phi1]

/-- `g5` acts on `φ₁(𝔽₁₆¹⁴)` as multiplication by `t` (Sec. 2.1). -/
theorem permute_g5_phi1 (c : Fin 14 → F16) : permute g5 (phi1 c) = phi1 (F16.t • c) := by
  funext i
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [permute_apply, g5_symm_E72, phi1_E72, phi1_E72]
  rcases z with ⟨a, b⟩ | x
  · rw [stdShift_symm_inl]
    simp only [phi1Z, Pi.smul_apply, smul_eq_mul]
    exact (psi_t_mul (c a) b).symm
  · rfl

theorem phi1_injective : Function.Injective phi1 := by
  intro c c' h
  funext a
  apply psi_injective
  funext b
  have := congrFun h (E72 (Sum.inl (a, b)))
  rwa [phi1_E72, phi1_E72] at this

/-- `⟨φ₁c, φ₁c'⟩ = Tr⟨c, c'⟩` with the Hermitian form `⟨c, c'⟩ = Σ_a c_a c̄'_a`. -/
theorem phi1_dot (c c' : Fin 14 → F16) : phi1 c ⬝ᵥ phi1 c' = tr (herm c c') := by
  simp only [dotProduct]
  rw [← Equiv.sum_comp E72, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [phi1_E72, phi1Z, mul_zero, Finset.sum_const_zero, add_zero]
  have h : ∀ a, ∑ b, psi (c a) b * psi (c' a) b = tr (c a * star (c' a)) := fun a => dot_psi _ _
  rw [Finset.sum_congr rfl (fun a _ => h a), herm, tr_sum]

/-- `φ₁c ⊥ φ₀u`: `ψ` has even weight on each cycle, and `φ₁c` vanishes on the fixed points. -/
theorem phi1_dot_phi0 (c : Fin 14 → F16) (u : Fin 16 → ZMod 2) : phi1 c ⬝ᵥ phi0 u = 0 := by
  simp only [dotProduct]
  rw [← Equiv.sum_comp E72, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [phi1_E72, phi0_E72, phi1Z, orb, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_mul, psi_sum, zero_mul]

/-! ## Weights -/

theorem wt_eq_sum {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : wt x = ∑ i, if x i = 0 then 0 else 1 := by
  rw [wt, hammingNorm, Finset.card_filter]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : x i = 0 <;> simp [h])

/-- The weight of `φ₀u + φ₁c`, cycle by cycle. -/
theorem wt_phi0_add_phi1 (u : Fin 16 → ZMod 2) (c : Fin 14 → F16) :
    wt (phi0 u + phi1 c) = ∑ a : Fin 14, wt (fun b => u (Fin.castAdd 2 a) + psi (c a) b) +
      ∑ x : Fin 2, (if u (Fin.natAdd 14 x) = 0 then 0 else 1) := by
  rw [wt_eq_sum, ← Equiv.sum_comp E72, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Pi.add_apply, phi0_E72, phi1_E72, phi1Z, orb, add_zero, wt_eq_sum]

/-- `φ₀u + φ₁c = 0` only for `c = 0`: the only constant word in the image of `ψ` is `0`. -/
theorem eq_zero_of_phi0_add_phi1 {u : Fin 16 → ZMod 2} {c : Fin 14 → F16} (h : phi0 u + phi1 c = 0) :
    c = 0 := by
  funext a
  apply psi_const (c a) (u (Fin.castAdd 2 a))
  intro b
  have hb := congrFun h (E72 (Sum.inl (a, b)))
  rw [Pi.add_apply, phi0_E72, phi1_E72, Pi.zero_apply] at hb
  simp only [orb, phi1Z] at hb
  have h2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact h2 _ _ hb

end C72.T3
