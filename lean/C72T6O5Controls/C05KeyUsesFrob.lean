import C72T6O5.Tests

/-!
# Control C05 (must not build): the key uses the Frobenius map

The row `C72T6O5.Tests.frobRow = (1 + t², 0, …, 0)` has pattern 3. Without the Frobenius map every image has pattern
at least 3 (`C72T6O5.Tests.collImages_frobRow`); with it the key is 2 (`C72T6O5.Tests.key_frobRow`, the positive
side). So the key is not 3. Expected failure: the kernel does not reduce the `Decidable` instance to `true`.
-/

open C72.T6O5 C72.T6O5.Tests

theorem C72.ControlsT6O5.c05_key_uses_frob : key frobRow = 3 := by
  decide +kernel
