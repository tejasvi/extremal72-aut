import C72T4.Codes36Check

/-!
# Control T4C05 (must not build): the pivot check detects a repeated row

`pivotCheck` holds for all 41 codes (`C72.T4.pivotCheck_all`). With the second row of `Y_0` replaced by its first row,
the first row has no pivot column, so the check must fail.
Expected failure: `decide` proves that the proposition `… = true` is false.
-/

open C72.T4

theorem C72.Controls.t4c05_corrupt_row_pivot :
    pivotCheckOn (fun r => if r = 1 then mask 0 0 else mask 0 r) = true := by
  decide +kernel
