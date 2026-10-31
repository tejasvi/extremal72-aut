import C72T3.F16
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin

/-!
# T3: the map `ψ`, the trace, the norm classes and the Hermitian form (Sec. 2.1)

* `psi y` is `ψ(y) = y(t) · (t + t² + t³ + t⁴)` in `𝔽₂[t]/(t⁵ − 1)`, a binary word of length 5 whose
  coordinate `b` is the coefficient of `t^b`. It is additive and injective, its image is the even-weight
  code of length 5 (`psi_sum`, `psi_psiInv`), and multiplication by `t` rotates it by one place
  (`psi_t_mul`), which is the action of the automorphism `g` on a cycle.
* `|ψ(y)| = 4` on `μ₅` and `2` on the other units (`wpsi_cls`).
* The binary inner product of `ψ(y)` and `ψ(y')` is `Tr(y ȳ')` (`dot_psi`), and the trace form is
  nondegenerate (`tr_nondeg`).
* The norm classes (Sec. 2.1): `cls y` is `0` for `y = 0`, `1` on `μ₅`, `2` on the class of `1 + t`, `3` on the
  class of `1 + t²` (`cls_reps`), and `y ȳ` depends only on the class (`norm_cls`).
* `herm x y = Σ_i x_i ȳ_i`, the Hermitian dual `hdual` and `HSelfDual`.

Every finite fact is checked by the kernel on all elements.
-/

namespace C72.T3

open Finset

namespace F16

/-- Rotation of a bit pattern of length 5 by `k` places: multiplication by `t^k` in `𝔽₂[t]/(t⁵ − 1)`. -/
def rot5 (p k : ℕ) : ℕ :=
  ((p <<< k) ||| (p >>> (5 - k))) &&& 31

/-- The product in `𝔽₂[t]/(t⁵ − 1)` of two bit patterns of length 5. -/
def cmul5 (p q : ℕ) : ℕ :=
  (bif q.testBit 0 then rot5 p 0 else 0) ^^^ (bif q.testBit 1 then rot5 p 1 else 0) ^^^
    (bif q.testBit 2 then rot5 p 2 else 0) ^^^ (bif q.testBit 3 then rot5 p 3 else 0) ^^^
    (bif q.testBit 4 then rot5 p 4 else 0)

end F16

open F16

/-! ## The map `ψ` -/

/-- `ψ(y) = y(t) · (t + t² + t³ + t⁴)` in `𝔽₂[t]/(t⁵ − 1)` (bit pattern `11110₂ = 30`), as a binary word of
length 5: coordinate `b` is the coefficient of `t^b`. -/
def psi (y : F16) : Fin 5 → ZMod 2 :=
  fun b => bif (cmul5 y.val.val 30).testBit b.val then 1 else 0

/-- `w(y) = |ψ(y)|`. -/
def wpsi (y : F16) : ℕ :=
  wt (psi y)

theorem psi_zero : psi 0 = 0 := by decide +kernel

theorem psi_add : ∀ a b : F16, psi (a + b) = psi a + psi b := by decide +kernel

theorem psi_injective : Function.Injective psi := by
  have h : ∀ a b : F16, psi a = psi b → a = b := by decide +kernel
  exact fun a b hab => h a b hab

/-- `ψ(y)` has even weight. -/
theorem psi_sum : ∀ y : F16, ∑ b, psi y b = 0 := by decide +kernel

/-- The only constant word in the image of `ψ` is `0`. -/
theorem psi_const : ∀ (y : F16) (s : ZMod 2), (∀ b, psi y b = s) → y = 0 := by decide +kernel

/-- Multiplication by `t` rotates `ψ(y)` by one place: `ψ(t y)_b = ψ(y)_{b-1}`. -/
theorem psi_t_mul : ∀ (y : F16) (b : Fin 5), psi (t * y) b = psi y ((finRotate 5).symm b) := by
  decide +kernel

/-- `|ψ(y)| ≤ 4`. -/
theorem wpsi_le : ∀ y : F16, wpsi y ≤ 4 := by decide +kernel

/-- The weight of `s · 11111 + ψ(y)`: `|ψ(y)|` if `s = 0`, and `5 − |ψ(y)|` if `s = 1`. -/
theorem wt_add_psi : ∀ (s : ZMod 2) (y : F16),
    wt (fun b => s + psi y b) = if s = 0 then wpsi y else 5 - wpsi y := by
  decide +kernel

/-- The inverse of `ψ` on even-weight words: `ψ(y) = z` gives `y_m = z_m + z_4` for `m < 4`. -/
def psiInv (z : Fin 5 → ZMod 2) : F16 :=
  ⟨⟨((z 0 + z 4).val + 2 * (z 1 + z 4).val + 4 * (z 2 + z 4).val + 8 * (z 3 + z 4).val) % 16,
    Nat.mod_lt _ (by decide)⟩⟩

theorem psi_psiInv' : ∀ z0 z1 z2 z3 z4 : ZMod 2, z0 + z1 + z2 + z3 + z4 = 0 →
    psi (psiInv ![z0, z1, z2, z3, z4]) = ![z0, z1, z2, z3, z4] := by
  decide +kernel

/-- Every even-weight word of length 5 is `ψ(y)` for `y = psiInv z`. -/
theorem psi_psiInv (z : Fin 5 → ZMod 2) (hz : ∑ b, z b = 0) : psi (psiInv z) = z := by
  have hz5 : z = ![z 0, z 1, z 2, z 3, z 4] := by
    funext b
    fin_cases b <;> rfl
  rw [Fin.sum_univ_five] at hz
  rw [hz5]
  exact psi_psiInv' _ _ _ _ _ hz

/-! ## The trace -/

/-- The absolute trace `Tr(z) = z + z² + z⁴ + z⁸`, which lies in `{0, 1}` (`tr_mem`); as an element of
`ZMod 2`. -/
def tr (z : F16) : ZMod 2 :=
  if z + z ^ 2 + z ^ 4 + z ^ 8 = 0 then 0 else 1

theorem tr_mem : ∀ z : F16, z + z ^ 2 + z ^ 4 + z ^ 8 = 0 ∨ z + z ^ 2 + z ^ 4 + z ^ 8 = 1 := by
  decide +kernel

theorem tr_add : ∀ a b : F16, tr (a + b) = tr a + tr b := by decide +kernel

theorem tr_zero : tr 0 = 0 := by decide +kernel

/-- The trace form is nondegenerate. -/
theorem tr_nondeg : ∀ z : F16, (∀ l : F16, tr (l * z) = 0) → z = 0 := by decide +kernel

/-- The binary inner product of `ψ(y)` and `ψ(y')` is `Tr(y ȳ')`. -/
theorem dot_psi : ∀ y y' : F16, psi y ⬝ᵥ psi y' = tr (y * star y') := by decide +kernel

/-- The trace as an additive map. -/
def trHom : F16 →+ ZMod 2 where
  toFun := tr
  map_zero' := tr_zero
  map_add' := tr_add

theorem trHom_apply (z : F16) : trHom z = tr z :=
  rfl

/-! ## Norm classes -/

/-- The norm `N(y) = y ȳ` is `y⁵`. -/
theorem norm_eq_pow : ∀ y : F16, y * star y = y ^ 5 := by decide +kernel

/-- The norm of `1 + t`, a primitive cube root of unity (an element of `𝔽₄ \ 𝔽₂`). -/
def nu2 : F16 := (1 + t) * star (1 + t)

/-- The norm of `1 + t²`, the other primitive cube root of unity. -/
def nu3 : F16 := (1 + t ^ 2) * star (1 + t ^ 2)

/-- The norm class of `y` (Sec. 2.1): `0` for `y = 0`, `1` on `μ₅`, `2` on the class of `1 + t`, `3` on the
class of `1 + t²`. The classes are the fibres of the norm on `𝔽₁₆^×`. -/
def cls (y : F16) : ℕ :=
  if y = 0 then 0 else if y * star y = 1 then 1 else if y * star y = nu2 then 2 else 3

theorem cls_lt : ∀ y : F16, cls y < 4 := by decide +kernel

theorem cls_eq_zero : ∀ y : F16, cls y = 0 ↔ y = 0 := by decide +kernel

/-- Class 1 is `μ₅ = {1, t, t², t³, t⁴}`. -/
theorem cls_eq_one : ∀ y : F16, cls y = 1 ↔ ∃ k, k < 5 ∧ y = t ^ k := by decide +kernel

/-- The representatives `1`, `1 + t`, `1 + t²` of the classes 1, 2, 3 (Sec. 2.1 and Lemma 2.5). -/
theorem cls_reps : cls 1 = 1 ∧ cls (1 + t) = 2 ∧ cls (1 + t ^ 2) = 3 := by decide +kernel

/-- The three norms `1`, `N(1 + t)`, `N(1 + t²)` are the three nonzero elements of `𝔽₄`: they are distinct
and their sum is `0`. -/
theorem norms_F4 : (1 : F16) ≠ nu2 ∧ (1 : F16) ≠ nu3 ∧ nu2 ≠ nu3 ∧ 1 + nu2 + nu3 = 0 ∧
    nu2 ^ 3 = 1 ∧ nu3 ^ 3 = 1 := by
  decide +kernel

/-- Each class has 5 elements. -/
theorem card_cls : ∀ c, c < 4 → 1 ≤ c → #(univ.filter fun y : F16 => cls y = c) = 5 := by decide +kernel

/-- `|ψ(y)| = 4` if `y ∈ μ₅`, `2` for the other units, `0` for `y = 0` (Sec. 2.1). -/
theorem wpsi_cls : ∀ y : F16, wpsi y = if y = 0 then 0 else if cls y = 1 then 4 else 2 := by
  decide +kernel

/-- The norm `y ȳ` as a function of the class: `Nc 0 = 0`, `Nc 1 = 1`, `Nc 2 = N(1 + t)`, `Nc 3 = N(1 + t²)`. -/
def Nc (c : ℕ) : F16 :=
  if c = 1 then 1 else if c = 2 then nu2 else if c = 3 then nu3 else 0

theorem norm_cls : ∀ y : F16, y * star y = Nc (cls y) := by decide +kernel

/-- With the classes coded as `0, 1, 2, 3`, the addition of norms is the exclusive or of the codes. -/
theorem Nc_xor : ∀ a, a < 4 → ∀ b, b < 4 → Nc (a ^^^ b) = Nc a + Nc b := by decide +kernel

theorem xor_lt_four : ∀ a, a < 4 → ∀ b, b < 4 → a ^^^ b < 4 := by decide +kernel

theorem Nc_eq_zero : ∀ a, a < 4 → (Nc a = 0 ↔ a = 0) := by decide +kernel

/-- The scaling used for class `r`: `λ₁ = 1`, `λ₂ = (1 + t)⁻¹`, `λ₃ = (1 + t²)⁻¹`. Multiplication by `λ_r` maps
class `r` onto `μ₅` (`wpsi_lam`). -/
def lam (r : ℕ) : F16 :=
  if r = 2 then (1 + t)⁻¹ else if r = 3 then (1 + t ^ 2)⁻¹ else 1

theorem lam_ne_zero : ∀ r, r < 4 → lam r ≠ 0 := by decide +kernel

/-- After the scaling by `λ_r`, an entry of class `c` has `|ψ| = 4` if `c = r`, `2` if `c ≠ r` is nonzero,
and `0` if `c = 0`. -/
theorem wpsi_lam : ∀ r, r < 4 → 1 ≤ r → ∀ y : F16,
    wpsi (lam r * y) = if cls y = 0 then 0 else if cls y = r then 4 else 2 := by
  decide +kernel

/-! ## The Hermitian form -/

/-- The Hermitian form `⟨x, y⟩ = Σ_i x_i ȳ_i` with `ȳ = y⁴` (Sec. 2.1). -/
def herm {ι : Type*} [Fintype ι] (x y : ι → F16) : F16 :=
  ∑ i, x i * star (y i)

section Herm

variable {ι : Type*} [Fintype ι]

theorem herm_add_left (x x' y : ι → F16) : herm (x + x') y = herm x y + herm x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_smul_left (a : F16) (x y : ι → F16) : herm (a • x) y = a * herm x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem herm_zero_left (y : ι → F16) : herm 0 y = 0 := by
  simp only [herm, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The Hermitian dual `D^{⊥_H} = {x | ∀ y ∈ D, ⟨x, y⟩ = 0}` of an `𝔽₁₆`-linear code. -/
def hdual (D : Submodule F16 (ι → F16)) : Submodule F16 (ι → F16) where
  carrier := {x | ∀ y ∈ D, herm x y = 0}
  add_mem' := by
    intro x x' hx hx' y hy
    rw [herm_add_left, hx y hy, hx' y hy, add_zero]
  zero_mem' := fun y _ => herm_zero_left y
  smul_mem' := by
    intro a x hx y hy
    rw [herm_smul_left, hx y hy, mul_zero]

theorem mem_hdual {D : Submodule F16 (ι → F16)} {x : ι → F16} :
    x ∈ hdual D ↔ ∀ y ∈ D, herm x y = 0 :=
  Iff.rfl

/-- `D` is Hermitian self-dual: `D = D^{⊥_H}`. -/
def HSelfDual (D : Submodule F16 (ι → F16)) : Prop :=
  D = hdual D

end Herm

end C72.T3
