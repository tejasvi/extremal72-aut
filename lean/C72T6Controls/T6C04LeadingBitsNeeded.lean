import C72T6.Refute

/-!
# Control T6C04 (must not build): the second test needs the leading bits

`C72.T6.lt_of_leading_bits_lt`: if `a / 2^t < b / 2^t` then `a < b`. The same with the bits below position `t`,
`a % 2^t < b % 2^t`, is false (`C72.T6.Refute.bits_need_leading`): `a = 4`, `b = 1`, `t = 2`.
Expected failure: `decide` proves that `4 % 2 ^ 2 < 1 % 2 ^ 2 → 4 < 1` is false.
-/

theorem C72.Controls.t6c04_leading_bits_needed : 4 % 2 ^ 2 < 1 % 2 ^ 2 → 4 < 1 := by
  decide
