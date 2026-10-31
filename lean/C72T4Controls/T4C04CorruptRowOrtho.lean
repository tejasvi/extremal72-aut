import C72T4.Codes36Check

/-!
# Control T4C04 (must not build): the orthogonality check detects a flipped bit

`orthoCheck` holds for all 41 codes (`C72.T4.orthoCheck_all`). With bit 0 of the first row of `Y_0` flipped, that row
has odd weight, so the check must fail.
Expected failure: `decide` proves that the proposition `… = true` is false.
-/

open C72.T4

theorem C72.Controls.t4c04_corrupt_row_ortho :
    orthoCheckOn (fun r => if r = 0 then mask 0 0 ^^^ 1 else mask 0 r) = true := by
  decide +kernel
