import C72T1.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# T2: the field `𝔽₄`, its conjugation and trace, and the map `ψ` (Section 4.1 of the paper)

`𝔽₄ = {0, 1, ω, ω̄}` with `ω̄ = ω² = ω + 1` is the inductive type `F4` with the constructors `zero`, `one`,
`w` (for `ω`) and `wb` (for `ω̄`). Addition, multiplication and inversion are tables, and the field axioms are
checked by `decide`. The conjugation is `star y = ȳ = y²` (`star_eq_sq`), and `tr` is the trace
`Tr(y) = y + y²` with values in `{0, 1} = 𝔽₂` (`tr_spec`).

`ψ : 𝔽₄ → 𝔽₂³` is the paper's dictionary `ψ(1) = 011`, `ψ(ω) = 101`, `ψ(ω̄) = 110`. It is additive and
injective; its image is the set of words of even weight (`psi_psiInv`); `|ψ(y)| = 2` for `y ≠ 0`
(`cycle_wt_psi`); multiplication by `ω` moves position `b - 1` to position `b` (`psi_w_mul`), which is the
action of `σ` on a cycle; and `⟨ψ(u), ψ(v)⟩ = Tr(u v̄)` (`psi_dot`, the trace identity).
-/

namespace C72

/-- The field `𝔽₄ = {0, 1, ω, ω̄}` with `ω̄ = ω² = ω + 1`: `zero`, `one`, `w` (`ω`) and `wb` (`ω̄`). -/
inductive F4 : Type
  | zero
  | one
  | w
  | wb
  deriving DecidableEq

namespace F4

instance : Fintype F4 where
  elems := {zero, one, w, wb}
  complete x := by cases x <;> decide

/-- Addition (characteristic 2): `x + x = 0`, `1 + ω = ω̄`, `1 + ω̄ = ω`, `ω + ω̄ = 1`. -/
def add : F4 → F4 → F4
  | zero, x => x
  | one, zero => one
  | one, one => zero
  | one, w => wb
  | one, wb => w
  | w, zero => w
  | w, one => wb
  | w, w => zero
  | w, wb => one
  | wb, zero => wb
  | wb, one => w
  | wb, w => one
  | wb, wb => zero

/-- Multiplication: `ω² = ω̄`, `ω ω̄ = 1`, `ω̄² = ω`. -/
def mul : F4 → F4 → F4
  | zero, _ => zero
  | one, x => x
  | w, zero => zero
  | w, one => w
  | w, w => wb
  | w, wb => one
  | wb, zero => zero
  | wb, one => wb
  | wb, w => one
  | wb, wb => w

/-- Inversion, with `0⁻¹ = 0` and `ω⁻¹ = ω̄`. -/
def inv : F4 → F4
  | zero => zero
  | one => one
  | w => wb
  | wb => w

instance : Zero F4 := ⟨zero⟩
instance : One F4 := ⟨one⟩
instance : Add F4 := ⟨add⟩
instance : Neg F4 := ⟨fun x => x⟩
instance : Mul F4 := ⟨mul⟩
instance : Inv F4 := ⟨inv⟩
instance : Nontrivial F4 := ⟨⟨zero, one, by decide⟩⟩

/-- `𝔽₄` is a commutative ring; every axiom is checked by `decide` on the tables. -/
instance instCommRing : CommRing F4 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide

/-- `𝔽₄` is a field (`x x⁻¹ = 1` for `x ≠ 0`, checked by `decide`). -/
instance instField : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem zero_def : (0 : F4) = zero := rfl
theorem one_def : (1 : F4) = one := rfl

/-- `ω² = ω̄`, `ω³ = 1` and `ω̄ = ω + 1`: the paper's description of `𝔽₄`. -/
theorem w_sq : w * w = wb ∧ w * w * w = 1 ∧ wb = w + 1 := by
  decide

/-- Conjugation `y ↦ ȳ`: it fixes `0` and `1` and swaps `ω` and `ω̄`. -/
def conj : F4 → F4
  | zero => zero
  | one => one
  | w => wb
  | wb => w

instance : Star F4 := ⟨conj⟩

/-- The conjugation is `ȳ = y²`, as in Section 4.1. -/
theorem star_eq_sq : ∀ y : F4, star y = y ^ 2 := by
  decide

/-- `x x̄ = 1` for `x ≠ 0`. -/
theorem mul_star_self : ∀ x : F4, x * star x = if x = 0 then 0 else 1 := by
  decide

/-- Conjugation is a field automorphism of order 2. -/
theorem star_add : ∀ x y : F4, star (x + y) = star x + star y := by
  decide

theorem star_mul : ∀ x y : F4, star (x * y) = star x * star y := by
  decide

theorem star_star : ∀ x : F4, star (star x) = x := by
  decide

theorem star_zero : star (0 : F4) = 0 :=
  rfl

/-- The trace `𝔽₄ → 𝔽₂`: `Tr(0) = Tr(1) = 0` and `Tr(ω) = Tr(ω̄) = 1`. -/
def tr : F4 → ZMod 2
  | zero => 0
  | one => 0
  | w => 1
  | wb => 1

/-- `tr` is the trace `Tr(y) = y + y²`, read in the prime field `{0, 1} ⊆ 𝔽₄`. -/
theorem tr_spec : ∀ y : F4, y + y ^ 2 = if tr y = 0 then 0 else 1 := by
  decide

theorem tr_add : ∀ u v : F4, tr (u + v) = tr u + tr v := by
  decide

theorem tr_zero : tr 0 = 0 :=
  rfl

/-- The trace as an additive map. -/
def trHom : F4 →+ ZMod 2 :=
  AddMonoidHom.mk' tr tr_add

theorem tr_sum {α : Type*} (s : Finset α) (f : α → F4) : tr (∑ i ∈ s, f i) = ∑ i ∈ s, tr (f i) :=
  map_sum trHom f s

/-- The trace form is nondegenerate: `Tr(z) = Tr(ω z) = 0` only for `z = 0`. -/
theorem eq_zero_of_tr : ∀ z : F4, tr z = 0 → tr (w * z) = 0 → z = 0 := by
  decide

/-- `ψ : 𝔽₄ → 𝔽₂³`: `ψ(0) = 000`, `ψ(1) = 011`, `ψ(ω) = 101`, `ψ(ω̄) = 110` (Section 4.1). -/
def psi : F4 → Fin 3 → ZMod 2
  | zero => ![0, 0, 0]
  | one => ![0, 1, 1]
  | w => ![1, 0, 1]
  | wb => ![1, 1, 0]

theorem psi_add : ∀ u v : F4, psi (u + v) = psi u + psi v := by
  decide

theorem psi_zero : psi 0 = 0 := by
  decide

theorem psi_injective : Function.Injective psi := by
  intro u v h
  revert u v h
  decide

/-- The action of `σ` on a cycle is multiplication by `ω`: `ψ(ω u)` has at position `b` the entry of `ψ(u)` at
position `b - 1`. -/
theorem psi_w_mul : ∀ (u : F4) (b : Fin 3), psi (w * u) b = psi u (b - 1) := by
  decide

/-- `ψ(y)` has even weight. -/
theorem psi_sum : ∀ u : F4, ∑ b : Fin 3, psi u b = 0 := by
  decide

/-- The same, summed along the cycle from any starting position. -/
theorem psi_cycle_sum : ∀ (u : F4) (b : Fin 3), psi u b + psi u (b + 1) + psi u (b + 1 + 1) = 0 := by
  decide

/-- `|ψ(y)| = 2` for `y ≠ 0` (and `0` for `y = 0`). -/
theorem cycle_wt_psi : ∀ u : F4,
    (∑ b : Fin 3, if psi u b ≠ 0 then 1 else 0) = 2 * (if u ≠ 0 then 1 else 0) := by
  decide

/-- The trace identity of Section 4.1: `⟨ψ(u), ψ(v)⟩ = Tr(u v̄)`. -/
theorem psi_dot : ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * star v) := by
  decide

/-- The same identity with Mathlib's `dotProduct`. -/
theorem psi_dotProduct (u v : F4) : psi u ⬝ᵥ psi v = tr (u * star v) :=
  psi_dot u v

/-- Both sides of the trace identity equal `1` exactly when `u` and `v` are nonzero and distinct. -/
theorem tr_mul_star : ∀ u v : F4, tr (u * star v) = if u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v then 1 else 0 := by
  decide

/-- The inverse of `ψ` on the words of length 3 of even weight. -/
def psiInv (v : Fin 3 → ZMod 2) : F4 :=
  if v 0 = 0 then (if v 1 = 0 then zero else one) else (if v 1 = 0 then w else wb)

theorem psi_psiInv : ∀ v : Fin 3 → ZMod 2, v 0 + v 1 + v 2 = 0 → psi (psiInv v) = v := by
  decide

/-- Lemma 4.1 on one cycle: `(x, x, x) + ψ(u)` has weight `0, 2, 3, 1` for `(x, u)` equal to `(0, 0)`,
`(0, ≠ 0)`, `(1, 0)`, `(1, ≠ 0)`, that is `3 [x ≠ 0] + 2 [u ≠ 0] - 4 [x ≠ 0 ∧ u ≠ 0]`. -/
theorem cycle_weight : ∀ (x : ZMod 2) (u : F4),
    (∑ b : Fin 3, if x + psi u b ≠ 0 then 1 else 0) + 4 * (if x ≠ 0 ∧ u ≠ 0 then 1 else 0) =
      3 * (if x ≠ 0 then 1 else 0) + 2 * (if u ≠ 0 then 1 else 0) := by
  decide

/-- The image of a natural number in `𝔽₄` is its parity. -/
theorem natCast_eq : ∀ n : ℕ, (n : F4) = if n % 2 = 0 then 0 else 1
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, natCast_eq n]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [ite_eq_left h, ite_eq_right (by omega)]
      decide
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      decide

end F4

end C72
