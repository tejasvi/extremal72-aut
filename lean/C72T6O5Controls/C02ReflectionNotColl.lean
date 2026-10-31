import C72T6O5.Coll

/-!
# Control C02 (must not build): the line check rejects a non-collineation

`C72T6O5.linesOK` accepts the 168 tables `tableOf a b c` (`triplesOK_eq_true`). The reflection `j ↦ -j` maps the
line `{0, 1, 3}` to `{0, 6, 4}`, which is not a line, so the check must return `false`. Expected failure:
`decide` proves the proposition false.
-/

open C72.T6O5

theorem C72.ControlsT6O5.c02_reflection_not_coll : linesOK ![0, 6, 5, 4, 3, 2, 1] = true := by
  decide +kernel
