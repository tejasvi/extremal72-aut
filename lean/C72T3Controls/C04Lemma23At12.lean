import C72T3.L23Check

/-!
# Control C04 (must not build): the check of Lemma 2.3 is not vacuous

At threshold 16 the check passes (`C72.T3.L23.chk16_0` to `chk16_3`, used by `C72.T3.lemma23`). At threshold 12
it fails (`C72.T3.L23.chk12_0`), so the claim that it passes must fail.
Expected failure: `decide` proves that `C72.T3.L23.chk 12 0 = true` is false.
-/

theorem C72.T3.Controls.c04_l23_at_12 : C72.T3.L23.chk 12 0 = true := by
  decide +kernel
