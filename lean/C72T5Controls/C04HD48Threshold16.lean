import C72T5Controls.HD48Check

/-!
# Control C04 (must not build): the kernel check of the length-48 analog of `H_D` with the threshold 16

The check with the threshold 12 passes (`C72.T5.HD48.go_all`): no nonzero word of `Y48` of weight below 12 has a bad
pattern. With the threshold 16 of `H_D` (length 72) in its place it must fail: the code of length 48 has words of
weight 12, and the first failing word in the order of `go` is the row `y_11` (weight 6) with the pattern
`e = {2, 9, 13}`, `6 + 2 · 3 = 12 < 16`.
Expected failure: `decide` proves that `go 16 12 0 0 0 = true` is false.
-/

open C72.T5.HD48

theorem C72.T5.Controls.c04_hd48_threshold_16 : go 16 12 0 0 0 = true := by
  decide +kernel
