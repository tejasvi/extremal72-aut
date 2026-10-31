import C72T2.F4

/-!
# Control C03 (must not build): the coefficient 4 in Lemma 4.1

`F4.cycle_weight` proves Lemma 4.1 on one cycle by `decide`: `cw x u + 4 [x ≠ 0 ∧ u ≠ 0] = 3 [x ≠ 0] + 2 [u ≠ 0]`,
where `cw x u` is the weight of `(x, x, x) + ψ(u)`. With `2` in place of `4` the same proof must fail (at `x = 1`,
`u ≠ 0` the word `(1, 1, 1) + ψ(u)` has weight 1, not 3).
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.F4

/-- The weight of `(x, x, x) + ψ(u)`, as in `F4.cycle_weight`. -/
def C72.ControlsT2.cw (x : ZMod 2) (u : F4) : ℕ :=
  ∑ b : Fin 3, if x + psi u b ≠ 0 then 1 else 0

/-- The indicator `[p]`. -/
def C72.ControlsT2.ind (p : Prop) [Decidable p] : ℕ :=
  if p then 1 else 0

open C72.ControlsT2 in
theorem C72.ControlsT2.c03_lemma41_coefficient : ∀ (x : ZMod 2) (u : F4),
    cw x u + 2 * ind (x ≠ 0 ∧ u ≠ 0) = 3 * ind (x ≠ 0) + 2 * ind (u ≠ 0) := by
  decide
