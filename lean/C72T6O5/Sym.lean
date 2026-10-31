import C72T6O5.Coll
import C72T3.Hyp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Relation

/-!
# T6 (order 5): the symmetries (a)-(c) of Sec. 2.4

On `7 × 7` matrices over `𝔽₁₆` (the rows are the coordinates of `A`, the columns those of `B`):

* (a) `U ↦ D₁⁻¹ U D₂` with `D₁`, `D₂` diagonal with entries in `μ₅` (`IsMu5Diag`);
* (b) `U ↦ P₁⁻¹ U P₂` with `P₁`, `P₂` the permutation matrices (`Equiv.Perm.permMatrix`) of collineations
  (`IsCollPerm`);
* (c) the Frobenius map `y ↦ y²` on all entries (`frobMat`).

`Step U V` says that `V` is the image of `U` under one of them; `Reach` is the reflexive-transitive closure, the
matrices obtained by finitely many symmetries. `Sol U` is the condition of Proposition 2.4: `UU* = I` (with `ȳ = y⁴`)
and `M(a) + M(aU) ≥ 16` for every nonzero `a`; `H_A` says that no matrix satisfies it (`H_A_iff_forall_not_sol`).

Each symmetry preserves `Sol` (`step_sol`, `reach_sol`). The paper explains this by coordinate permutations of the
length-72 code; here it is proved directly: the scalings in (a) and the Frobenius map are unitary on rows and columns,
`M` depends only on `|ψ|` of the entries, which `μ₅`-scaling and the Frobenius map preserve, and collineations preserve
`M` (`M_comp`).
-/

namespace C72.T6O5

open C72.T3 Finset Equiv Matrix

/-- `D` is diagonal with entries in `μ₅`, the fifth roots of unity. -/
def IsMu5Diag (D : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  ∃ d : Fin 7 → F16, (∀ i, d i ^ 5 = 1) ∧ D = diagonal d

/-- `P` is the permutation matrix of a collineation of the Fano plane. -/
def IsCollPerm (P : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  ∃ σ : Perm (Fin 7), IsColl σ ∧ P = σ.permMatrix F16

/-- The Frobenius map `y ↦ y²` on all entries. -/
def frobMat (U : Matrix (Fin 7) (Fin 7) F16) : Matrix (Fin 7) (Fin 7) F16 :=
  U.map fun y => y ^ 2

/-- `V` is the image of `U` under one of the symmetries (a), (b), (c) of Sec. 2.4. -/
def Step (U V : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  (∃ D₁ D₂, IsMu5Diag D₁ ∧ IsMu5Diag D₂ ∧ V = D₁⁻¹ * U * D₂) ∨
    (∃ P₁ P₂, IsCollPerm P₁ ∧ IsCollPerm P₂ ∧ V = P₁⁻¹ * U * P₂) ∨ V = frobMat U

/-- `V` is obtained from `U` by finitely many symmetries (a)-(c). -/
def Reach : Matrix (Fin 7) (Fin 7) F16 → Matrix (Fin 7) (Fin 7) F16 → Prop :=
  Relation.ReflTransGen Step

/-- The conditions of Proposition 2.4 on `U`: `UU* = I` and `M(a) + M(aU) ≥ 16` for every nonzero `a`. -/
def Sol (U : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  U * Uᴴ = 1 ∧ ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* U)

/-- `H_A` (T3) says exactly that no matrix satisfies the conditions of Proposition 2.4. -/
theorem H_A_iff_forall_not_sol : H_A ↔ ∀ U, ¬ Sol U := by
  constructor
  · rintro h U ⟨hU, hM⟩
    obtain ⟨a, ha, hlt⟩ := h U hU
    have := hM a ha
    omega
  · intro h U hU
    by_contra hc
    exact h U ⟨hU, fun a ha => by
      by_contra hlt
      exact hc ⟨a, ha, by omega⟩⟩

theorem reach_refl (U : Matrix (Fin 7) (Fin 7) F16) : Reach U U :=
  Relation.ReflTransGen.refl

theorem reach_of_step {U V : Matrix (Fin 7) (Fin 7) F16} (h : Step U V) : Reach U V :=
  Relation.ReflTransGen.single h

theorem reach_tail {U V W : Matrix (Fin 7) (Fin 7) F16} (h : Reach U V) (h' : Step V W) : Reach U W :=
  Relation.ReflTransGen.tail h h'

theorem reach_trans {U V W : Matrix (Fin 7) (Fin 7) F16} (h : Reach U V) (h' : Reach V W) : Reach U W :=
  Relation.ReflTransGen.trans h h'

/-! ## Finite facts on `𝔽₁₆` -/

theorem mu5_ne_zero : ∀ y : F16, y ^ 5 = 1 → y ≠ 0 := by decide +kernel

theorem mu5_inv : ∀ y : F16, y ^ 5 = 1 → y⁻¹ ^ 5 = 1 := by decide +kernel

theorem mu5_mul (y z : F16) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1) : (y * z) ^ 5 = 1 := by
  rw [mul_pow, hy, hz, one_mul]

theorem mu5_mul_star : ∀ y : F16, y ^ 5 = 1 → y * star y = 1 := by decide +kernel

theorem wpsi_mul_mu5 : ∀ y z : F16, z ^ 5 = 1 → wpsi (y * z) = wpsi y := by decide +kernel

theorem cls_mul_mu5 : ∀ y z : F16, z ^ 5 = 1 → cls (y * z) = cls y := by decide +kernel

theorem wpsi_sq : ∀ y : F16, wpsi (y ^ 2) = wpsi y := by decide +kernel

theorem sq_add : ∀ x y : F16, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by decide +kernel

theorem star_sq : ∀ y : F16, star (y ^ 2) = star y ^ 2 := by decide +kernel

theorem pow_eight_sq : ∀ y : F16, (y ^ 8) ^ 2 = y := by decide +kernel

/-- The Frobenius map `y ↦ y²` as a ring homomorphism. -/
def frobHom : F16 →+* F16 where
  toFun y := y ^ 2
  map_one' := one_pow 2
  map_mul' x y := mul_pow x y 2
  map_zero' := by decide
  map_add' := sq_add

theorem perm_inv_apply_self (p : Perm (Fin 7)) (i : Fin 7) : p⁻¹ (p i) = i :=
  Perm.inv_eq_iff_eq.2 rfl

theorem perm_apply_inv_self (p : Perm (Fin 7)) (i : Fin 7) : p (p⁻¹ i) = i :=
  (Perm.eq_inv_iff_eq.1 rfl)

/-! ## The entries after a symmetry -/

theorem inv_diagonal_mu5 {d : Fin 7 → F16} (hd : ∀ i, d i ^ 5 = 1) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  apply inv_eq_left_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (mu5_ne_zero _ (hd i))

theorem inv_permMatrix (σ : Perm (Fin 7)) : (σ.permMatrix F16)⁻¹ = σ⁻¹.permMatrix F16 := by
  apply inv_eq_left_inv
  rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

/-- The entries after (a): `(D₁⁻¹ U D₂)_{ij} = d₁(i)⁻¹ U_{ij} d₂(j)`. -/
theorem scale_apply {d₁ d₂ : Fin 7 → F16} (h₁ : ∀ i, d₁ i ^ 5 = 1) (U : Matrix (Fin 7) (Fin 7) F16) (i j : Fin 7) :
    ((diagonal d₁)⁻¹ * U * diagonal d₂) i j = (d₁ i)⁻¹ * U i j * d₂ j := by
  rw [inv_diagonal_mu5 h₁, mul_diagonal, diagonal_mul]

/-- The entries after (b): `(P_σ⁻¹ U P_τ)_{ij} = U_{σ⁻¹(i), τ⁻¹(j)}`. -/
theorem perm_apply (σ τ : Perm (Fin 7)) (U : Matrix (Fin 7) (Fin 7) F16) (i j : Fin 7) :
    ((σ.permMatrix F16)⁻¹ * U * τ.permMatrix F16) i j = U (σ⁻¹ i) (τ⁻¹ j) := by
  rw [inv_permMatrix, Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem step_scale (d₁ d₂ : Fin 7 → F16) (h₁ : ∀ i, d₁ i ^ 5 = 1) (h₂ : ∀ j, d₂ j ^ 5 = 1)
    (U : Matrix (Fin 7) (Fin 7) F16) : Step U ((diagonal d₁)⁻¹ * U * diagonal d₂) :=
  Or.inl ⟨_, _, ⟨d₁, h₁, rfl⟩, ⟨d₂, h₂, rfl⟩, rfl⟩

theorem step_perm {σ τ : Perm (Fin 7)} (hσ : IsColl σ) (hτ : IsColl τ) (U : Matrix (Fin 7) (Fin 7) F16) :
    Step U ((σ.permMatrix F16)⁻¹ * U * τ.permMatrix F16) :=
  Or.inr (Or.inl ⟨_, _, ⟨σ, hσ, rfl⟩, ⟨τ, hτ, rfl⟩, rfl⟩)

theorem step_frob (U : Matrix (Fin 7) (Fin 7) F16) : Step U (frobMat U) :=
  Or.inr (Or.inr rfl)

/-! ## `UU* = I` is preserved -/

theorem mul_conjTranspose_self_apply (V : Matrix (Fin 7) (Fin 7) F16) (i k : Fin 7) :
    (V * Vᴴ) i k = ∑ j, V i j * star (V k j) := by
  simp only [mul_apply, conjTranspose_apply]

theorem unitary_of_scale {U V : Matrix (Fin 7) (Fin 7) F16} {e₁ e₂ : Fin 7 → F16} (h₁ : ∀ i, e₁ i ^ 5 = 1)
    (h₂ : ∀ j, e₂ j ^ 5 = 1) (hV : ∀ i j, V i j = e₁ i * U i j * e₂ j) (hU : U * Uᴴ = 1) : V * Vᴴ = 1 := by
  ext i k
  have hUik := congrFun (congrFun hU i) k
  rw [mul_conjTranspose_self_apply] at hUik ⊢
  have hsum : ∑ j, V i j * star (V k j) = e₁ i * star (e₁ k) * ∑ j, U i j * star (U k j) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [hV, hV, F16.star_mul, F16.star_mul]
    calc e₁ i * U i j * e₂ j * (star (e₁ k) * star (U k j) * star (e₂ j))
        = e₁ i * star (e₁ k) * (U i j * star (U k j)) * (e₂ j * star (e₂ j)) := by ring
      _ = e₁ i * star (e₁ k) * (U i j * star (U k j)) := by rw [mu5_mul_star _ (h₂ j), mul_one]
  rw [hsum, hUik]
  by_cases hik : i = k
  · subst hik
    rw [one_apply_eq, mul_one, mu5_mul_star _ (h₁ i)]
  · rw [one_apply_ne hik, mul_zero]

theorem unitary_of_perm {U V : Matrix (Fin 7) (Fin 7) F16} (p q : Perm (Fin 7))
    (hV : ∀ i j, V i j = U (p i) (q j)) (hU : U * Uᴴ = 1) : V * Vᴴ = 1 := by
  ext i k
  have hUik := congrFun (congrFun hU (p i)) (p k)
  rw [mul_conjTranspose_self_apply] at hUik ⊢
  have e : ∑ j, V i j * star (V k j) = ∑ j, U (p i) j * star (U (p k) j) := by
    simp only [hV]
    exact Equiv.sum_comp q (fun j => U (p i) j * star (U (p k) j))
  rw [e, hUik]
  by_cases hik : i = k
  · subst hik
    rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne hik, one_apply_ne (p.injective.ne hik)]

theorem unitary_frob {U : Matrix (Fin 7) (Fin 7) F16} (hU : U * Uᴴ = 1) : frobMat U * (frobMat U)ᴴ = 1 := by
  ext i k
  have hUik := congrFun (congrFun hU i) k
  rw [mul_conjTranspose_self_apply] at hUik ⊢
  have e : ∑ j, frobMat U i j * star (frobMat U k j) = frobHom (∑ j, U i j * star (U k j)) := by
    rw [map_sum]
    refine sum_congr rfl fun j _ => ?_
    show U i j ^ 2 * star (U k j ^ 2) = (U i j * star (U k j)) ^ 2
    rw [star_sq, mul_pow]
  rw [e, hUik]
  by_cases hik : i = k
  · subst hik
    rw [one_apply_eq]
    exact map_one frobHom
  · rw [one_apply_ne hik]
    exact map_zero frobHom

/-! ## The condition `M(a) + M(aU) ≥ 16` is preserved -/

theorem M_congr {v v' : Fin 7 → F16} (h : ∀ i, wpsi (v i) = wpsi (v' i)) : M v = M v' := by
  have h' : (fun i => wpsi (v i)) = fun i => wpsi (v' i) := funext h
  unfold M
  rw [h']

theorem cond_of_scale {U V : Matrix (Fin 7) (Fin 7) F16} {e₁ e₂ : Fin 7 → F16} (h₁ : ∀ i, e₁ i ^ 5 = 1)
    (h₂ : ∀ j, e₂ j ^ 5 = 1) (hV : ∀ i j, V i j = e₁ i * U i j * e₂ j)
    (hU : ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* U)) :
    ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* V) := by
  intro a ha
  have ha' : (fun i => a i * e₁ i) ≠ 0 := by
    intro h0
    apply ha
    funext i
    have hi : a i * e₁ i = 0 := congrFun h0 i
    exact (mul_eq_zero.1 hi).resolve_right (mu5_ne_zero _ (h₁ i))
  have hMa : M a = M (fun i => a i * e₁ i) := M_congr fun i => (wpsi_mul_mu5 _ _ (h₁ i)).symm
  have hvec : ∀ j, (a ᵥ* V) j = ((fun i => a i * e₁ i) ᵥ* U) j * e₂ j := by
    intro j
    simp only [vecMul, dotProduct, hV, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  have hMb : M (a ᵥ* V) = M ((fun i => a i * e₁ i) ᵥ* U) :=
    M_congr fun j => by rw [hvec, wpsi_mul_mu5 _ _ (h₂ j)]
  rw [hMa, hMb]
  exact hU _ ha'

theorem cond_of_perm {U V : Matrix (Fin 7) (Fin 7) F16} {p q : Perm (Fin 7)} (hp : IsColl p) (hq : IsColl q)
    (hV : ∀ i j, V i j = U (p i) (q j)) (hU : ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* U)) :
    ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* V) := by
  intro a ha
  have ha' : (fun k => a (p⁻¹ k)) ≠ 0 := by
    intro h0
    apply ha
    funext i
    have hi : a (p⁻¹ (p i)) = 0 := congrFun h0 (p i)
    rwa [perm_inv_apply_self] at hi
  have hMa : M a = M (fun k => a (p⁻¹ k)) := by
    rw [← M_comp hp (fun k => a (p⁻¹ k))]
    simp only [perm_inv_apply_self]
  have hvec : a ᵥ* V = fun j => ((fun k => a (p⁻¹ k)) ᵥ* U) (q j) := by
    funext j
    simp only [vecMul, dotProduct, hV]
    rw [← Equiv.sum_comp p (fun k => a (p⁻¹ k) * U k (q j))]
    simp only [perm_inv_apply_self]
  have hMb : M (a ᵥ* V) = M ((fun k => a (p⁻¹ k)) ᵥ* U) := by
    rw [hvec, M_comp hq]
  rw [hMa, hMb]
  exact hU _ ha'

theorem cond_frob {U : Matrix (Fin 7) (Fin 7) F16} (hU : ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* U)) :
    ∀ a : Fin 7 → F16, a ≠ 0 → 16 ≤ M a + M (a ᵥ* frobMat U) := by
  intro a ha
  have ha' : (fun i => a i ^ 8) ≠ 0 := by
    intro h0
    apply ha
    funext i
    have hi : a i ^ 8 = 0 := congrFun h0 i
    show a i = 0
    rw [← pow_eight_sq (a i), hi]
    decide
  have hMa : M a = M (fun i => a i ^ 8) := M_congr fun i => by rw [← wpsi_sq (a i ^ 8), pow_eight_sq]
  have hvec : ∀ j, (a ᵥ* frobMat U) j = ((fun i => a i ^ 8) ᵥ* U) j ^ 2 := by
    intro j
    simp only [vecMul, dotProduct]
    show ∑ i, a i * U i j ^ 2 = (∑ i, a i ^ 8 * U i j) ^ 2
    have hf : (∑ i, a i ^ 8 * U i j) ^ 2 = frobHom (∑ i, a i ^ 8 * U i j) := rfl
    rw [hf, map_sum]
    refine sum_congr rfl fun i _ => ?_
    show a i * U i j ^ 2 = (a i ^ 8 * U i j) ^ 2
    rw [mul_pow, pow_eight_sq]
  have hMb : M (a ᵥ* frobMat U) = M ((fun i => a i ^ 8) ᵥ* U) := M_congr fun j => by rw [hvec, wpsi_sq]
  rw [hMa, hMb]
  exact hU _ ha'

/-! ## Each symmetry preserves the conditions of Proposition 2.4 -/

theorem step_sol {U V : Matrix (Fin 7) (Fin 7) F16} (h : Step U V) (hU : Sol U) : Sol V := by
  rcases h with ⟨D₁, D₂, ⟨d₁, hd₁, rfl⟩, ⟨d₂, hd₂, rfl⟩, rfl⟩ | ⟨P₁, P₂, ⟨σ, hσ, rfl⟩, ⟨τ, hτ, rfl⟩, rfl⟩ | rfl
  · have hV := scale_apply (d₂ := d₂) hd₁ U
    exact ⟨unitary_of_scale (fun i => mu5_inv _ (hd₁ i)) hd₂ hV hU.1,
      cond_of_scale (fun i => mu5_inv _ (hd₁ i)) hd₂ hV hU.2⟩
  · have hV := perm_apply σ τ U
    exact ⟨unitary_of_perm _ _ hV hU.1, cond_of_perm (isColl_inv hσ) (isColl_inv hτ) hV hU.2⟩
  · exact ⟨unitary_frob hU.1, cond_frob hU.2⟩

theorem reach_sol {U V : Matrix (Fin 7) (Fin 7) F16} (h : Reach U V) (hU : Sol U) : Sol V := by
  unfold Reach at h
  induction h with
  | refl => exact hU
  | tail _ hst ih => exact step_sol hst ih

end C72.T6O5
