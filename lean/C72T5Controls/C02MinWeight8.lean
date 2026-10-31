import C72T5.CB48Check

/-!
# Control C02 (must not build): the code `E48` has minimum weight 6, not 8

The check with the bound 6 passes (`C72.T5.CB48.go_all`), and `E48` has words of weight 6
(`C72.T5.CB48.wt_erow1`). With the bound 8 it must fail.
Expected failure: `decide` proves that `go tets octs 8 8 0 0 0 = true` is false.
-/

open C72.T5.CB48

theorem C72.T5.Controls.c02_min_weight_8 : go tets octs 8 8 0 0 0 = true := by
  decide +kernel
