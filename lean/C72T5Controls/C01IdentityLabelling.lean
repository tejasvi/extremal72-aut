import C72T5.CB48Check

/-!
# Control C01 (must not build): the check of the length-48 analog of `H_CB` is not vacuous

With the labelling `piCB` every word of `E48` passes (`C72.T5.CB48.go_all`, used by `C72.T5.not_H_CB48`). Without
the labelling (`π = 1`: the tetrads and octads of `e8 ⊕ e8` in their own coordinates, `tetsStd`, `octsStd`) some word
of weight 6 contains a tetrad or some word of weight 8 has an octad as support, so the claim that all words pass must
fail.
Expected failure: `decide` proves that `go tetsStd octsStd 6 8 0 0 0 = true` is false.
-/

open C72.T5.CB48

theorem C72.T5.Controls.c01_identity_labelling : go tetsStd octsStd 6 8 0 0 0 = true := by
  decide +kernel
