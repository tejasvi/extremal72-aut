import C72T1.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Fintype.OfMap
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime

/-!
# T3: the field `𝔽₁₆` of Sec. 2.1

`𝔽₁₆ = 𝔽₂[t]/(t⁴ + t³ + t² + t + 1)`. An element is stored as the bit pattern of its coefficients in the
basis `1, t, t², t³`: bit `k` of `val` is the coefficient of `t^k`. Addition is the exclusive or of the
patterns; multiplication is the product of the polynomials over `𝔽₂`, reduced modulo
`t⁴ + t³ + t² + t + 1`.

* The field axioms are checked by the kernel on all elements (`decide +kernel`), so `F16` is a Mathlib
  `Field` (`instField`). Mathlib's `GaloisField` is not computable and is not used.
* `t⁴ + t³ + t² + t + 1 = 0` (`t_minpoly`) and `x = x₀ + x₁ t + x₂ t² + x₃ t³` with `xₖ` the bits of `x`
  (`eq_poly`): this is `𝔽₂[t]/(t⁴ + t³ + t² + t + 1)` with the bits as coordinates.
* `t` has multiplicative order 5 (`orderOf_t`), so `t` is not a primitive element.
* The conjugation is `ȳ = y⁴` (the `Star` instance), an automorphism of order 2 (`star_star`, `star_add`,
  `star_mul`), not the Frobenius `y ↦ y²`.
-/

namespace C72.T3

/-- An element of `𝔽₁₆`: bit `k` of `val` is the coefficient of `t^k` (`k < 4`). -/
structure F16 where
  /-- The bit pattern of the coefficients. -/
  val : Fin 16
  deriving DecidableEq

namespace F16

/-- `F16 ≃ Fin 16` (the bit patterns). -/
def equivFin : F16 ≃ Fin 16 where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype F16 :=
  Fintype.ofEquiv (Fin 16) equivFin.symm

/-! ### Arithmetic of bit patterns -/

/-- The product of two polynomials over `𝔽₂` of degree `< 4`, given by their bit patterns. -/
def clmul (a b : ℕ) : ℕ :=
  (bif b.testBit 0 then a else 0) ^^^ (bif b.testBit 1 then a <<< 1 else 0) ^^^
    (bif b.testBit 2 then a <<< 2 else 0) ^^^ (bif b.testBit 3 then a <<< 3 else 0)

/-- Reduction of a polynomial of degree `≤ 6` modulo `t⁴ + t³ + t² + t + 1` (bit pattern `31`). -/
def reduce (p : ℕ) : ℕ :=
  let p₁ := bif p.testBit 6 then p ^^^ (31 <<< 2) else p
  let p₂ := bif p₁.testBit 5 then p₁ ^^^ (31 <<< 1) else p₁
  bif p₂.testBit 4 then p₂ ^^^ 31 else p₂

/-- Addition: the exclusive or of the bit patterns. -/
def add (a b : F16) : F16 :=
  ⟨⟨(a.val.val ^^^ b.val.val) % 16, Nat.mod_lt _ (by decide)⟩⟩

/-- Multiplication: the product of the polynomials, reduced modulo `t⁴ + t³ + t² + t + 1`. -/
def mul (a b : F16) : F16 :=
  ⟨⟨reduce (clmul a.val.val b.val.val) % 16, Nat.mod_lt _ (by decide)⟩⟩

/-- The inverse `a⁻¹ = a¹⁴` (so `0⁻¹ = 0`). -/
def inv (a : F16) : F16 :=
  let a2 := mul a a
  let a4 := mul a2 a2
  let a8 := mul a4 a4
  mul (mul a8 a4) a2

instance : Zero F16 := ⟨⟨0⟩⟩
instance : One F16 := ⟨⟨1⟩⟩
instance : Add F16 := ⟨add⟩
instance : Mul F16 := ⟨mul⟩
/-- Negation is the identity (characteristic 2). -/
instance : Neg F16 := ⟨id⟩
instance : Inv F16 := ⟨inv⟩

/-! ### The field axioms, checked on all elements -/

theorem add_assoc' : ∀ a b c : F16, a + b + c = a + (b + c) := by decide +kernel
theorem add_comm' : ∀ a b : F16, a + b = b + a := by decide +kernel
theorem zero_add' : ∀ a : F16, 0 + a = a := by decide +kernel
theorem add_zero' : ∀ a : F16, a + 0 = a := by decide +kernel
theorem neg_add_cancel' : ∀ a : F16, -a + a = 0 := by decide +kernel
theorem mul_assoc' : ∀ a b c : F16, a * b * c = a * (b * c) := by decide +kernel
theorem mul_comm' : ∀ a b : F16, a * b = b * a := by decide +kernel
theorem one_mul' : ∀ a : F16, 1 * a = a := by decide +kernel
theorem mul_one' : ∀ a : F16, a * 1 = a := by decide +kernel
theorem zero_mul' : ∀ a : F16, 0 * a = 0 := by decide +kernel
theorem mul_zero' : ∀ a : F16, a * 0 = 0 := by decide +kernel
theorem left_distrib' : ∀ a b c : F16, a * (b + c) = a * b + a * c := by decide +kernel
theorem right_distrib' : ∀ a b c : F16, (a + b) * c = a * c + b * c := by decide +kernel
theorem mul_inv_cancel' : ∀ a : F16, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
theorem inv_zero' : (0 : F16)⁻¹ = 0 := by decide +kernel

/-- `𝔽₁₆` is a field. -/
instance instField : Field F16 where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec
  add_comm := add_comm'
  mul := (· * ·)
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_assoc := mul_assoc'
  one := 1
  one_mul := one_mul'
  mul_one := mul_one'
  neg := Neg.neg
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel'
  mul_comm := mul_comm'
  inv := Inv.inv
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The conjugation `ȳ = y⁴` of Sec. 2.1, not the Frobenius `y ↦ y²`. -/
instance : Star F16 := ⟨fun y => y ^ 4⟩

theorem star_def (y : F16) : star y = y ^ 4 :=
  rfl

/-! ### The element `t` and the polynomial basis -/

/-- The class of `t` (bit pattern `0010`). -/
def t : F16 := ⟨2⟩

/-- The coefficient of `t^k` in `x`, as an element of `𝔽₁₆` (`0` or `1`). -/
def coeff (x : F16) (k : ℕ) : F16 :=
  bif x.val.val.testBit k then 1 else 0

/-- `t` is a root of `t⁴ + t³ + t² + t + 1`. -/
theorem t_minpoly : t ^ 4 + t ^ 3 + t ^ 2 + t + 1 = 0 := by decide +kernel

/-- Every element is `x₀ + x₁ t + x₂ t² + x₃ t³`, with `xₖ` the bits of its pattern. -/
theorem eq_poly : ∀ x : F16, x = coeff x 0 + coeff x 1 * t + coeff x 2 * t ^ 2 + coeff x 3 * t ^ 3 := by
  decide +kernel

theorem t_pow_five : t ^ 5 = 1 := by decide +kernel

theorem t_ne_one : t ≠ 1 := by decide

/-- `t` has multiplicative order 5; it is not a primitive element of `𝔽₁₆^×`. -/
theorem orderOf_t : orderOf t = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime t_pow_five t_ne_one

theorem card_eq : Fintype.card F16 = 16 := by decide +kernel

/-- Characteristic 2. -/
theorem add_self : ∀ a : F16, a + a = 0 := by decide +kernel

/-- The conjugation has order 2. -/
theorem star_star : ∀ y : F16, star (star y) = y := by decide +kernel

theorem star_add : ∀ x y : F16, star (x + y) = star x + star y := by decide +kernel

theorem star_mul : ∀ x y : F16, star (x * y) = star x * star y := by decide +kernel

/-- The Frobenius `y ↦ y²` is not the conjugation: it moves `t` to `t²`, while `t̄ = t⁴`. -/
theorem star_t : star t = t ^ 4 ∧ t ^ 2 ≠ t ^ 4 := by decide +kernel

end F16

end C72.T3
