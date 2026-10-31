import C72T6O5.Tests

/-!
# Control C01 (must not build): the key is not the pattern in general

`C72T6O5.keyRow_key` checks that the pattern of each depth-0 row of Table 1 is its key. The row of key 0 read
backwards (`C72T6O5.Tests.revRow`, pattern `0111123`) is not the smallest pattern in its orbit: a collineation moves
its zero entry to column 6. Positive side: `C72T6O5.Tests.key_lt_pattern_revRow`. Expected failure: the kernel does
not reduce the `Decidable` instance to `true`.
-/

open C72.T6O5 C72.T6O5.Tests

theorem C72.ControlsT6O5.c01_key_not_pattern : key revRow = pattern revRow := by
  decide +kernel
