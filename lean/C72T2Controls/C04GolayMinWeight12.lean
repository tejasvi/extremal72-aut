import C72T2.Golay

/-!
# Control C04 (must not build): the 4096-word check is not vacuous

`Three.g24_chk` checks with `chk` that every nonzero word of `G24` has weight 8, 12, 16 or 24. The same check with
the weights 12, 16, 24 only (a claim of minimum weight 12) must fail.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three

/-- `okWt` without the weight 8. -/
def C72.ControlsT2.okWt12 (n : ℕ) : Bool :=
  n == 12 || n == 16 || n == 24

/-- `chk` with `okWt12`. -/
def C72.ControlsT2.chk12 : (k : ℕ) → (Fin k → ℕ) → Bool → ℕ → Bool
  | 0, _, nz, acc => !nz || C72.ControlsT2.okWt12 (wt (toVec acc))
  | k + 1, ms, nz, acc =>
    C72.ControlsT2.chk12 k (Fin.tail ms) nz acc && C72.ControlsT2.chk12 k (Fin.tail ms) true (acc ^^^ ms 0)

theorem C72.ControlsT2.c04_golay_min_weight_12 : C72.ControlsT2.chk12 12 g24mask false 0 = true := by
  decide
