import C72T3.E8
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# T3: the named hypotheses of Theorem A

Each is a `def … : Prop`; none is an axiom. They are explicit premises of `C72.thmA_of_hyps`
(`C72T3.ThmA`). The list below gives the source of each; none says more than its
source.

* `H_CP5` (cited, [CP82]; see also [FN12, §V.A]): an automorphism of order 5 has exactly two fixed points.
* `H_16` (cited): every doubly-even self-dual code of length 16 is equivalent to `e8 ⊕ e8` or to `d₁₆⁺`.
* `H_A` (computation, Proposition 2.4): for every `7 × 7` matrix `U` over `𝔽₁₆` with `UU* = I` (with the
  conjugation `ȳ = y⁴`) some nonzero `a` has `M(a) + M(aU) < 16`.

`H_Athr d` is `H_A` with the threshold `d` in place of 16, for the controls; `H_A` is `H_Athr 16`
(`H_A_iff`).
-/

namespace C72

open Matrix

/-- **H_CP5** (cited, [CP82]; see also [FN12, §V.A]): an automorphism of order 5 of a doubly-even self-dual
`[72,36,16]` code has exactly two fixed points. -/
def H_CP5 : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g = 5 → (Finset.univ.filter fun i => g i = i).card = 2

/-- **H_16** (cited; the classification of doubly-even self-dual codes of length 16, used in the proof of
Lemma 2.1): every doubly-even self-dual code of length 16 is equivalent to `e8 ⊕ e8` or to `d₁₆⁺`. Source: the
classification of the doubly-even self-dual codes of length 16 with the mass formula [RS98]; the consequence used
is [FN12, Lemma 5.1]. -/
def H_16 : Prop :=
  ∀ D : Code 16, TypeII D → PermEquiv D T3.e8e8 ∨ PermEquiv D T3.d16plus

/-- **H_A** (computation, Proposition 2.4): there is no `7 × 7` matrix `U` over `𝔽₁₆` with `UU* = I` such that
`M(a) + M(aU) ≥ 16` for every nonzero `a ∈ 𝔽₁₆⁷`. Here `U*` is `Uᴴ`, the conjugate transpose for `ȳ = y⁴`,
`a ᵥ* U` is the row vector `aU`, and `M` is the function of Sec. 2.3 (`C72.T3.M`). -/
def H_A : Prop :=
  ∀ U : Matrix (Fin 7) (Fin 7) T3.F16, U * Uᴴ = 1 → ∃ a : Fin 7 → T3.F16, a ≠ 0 ∧ T3.M a + T3.M (a ᵥ* U) < 16

/-- `H_A` with the threshold `d` in place of 16 (for the controls). -/
def H_Athr (d : ℕ) : Prop :=
  ∀ U : Matrix (Fin 7) (Fin 7) T3.F16, U * Uᴴ = 1 → ∃ a : Fin 7 → T3.F16, a ≠ 0 ∧ T3.M a + T3.M (a ᵥ* U) < d

theorem H_A_iff : H_A ↔ H_Athr 16 :=
  Iff.rfl

end C72
