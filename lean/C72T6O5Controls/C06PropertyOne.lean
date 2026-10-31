import C72T6O5.Tests

/-!
# Control C06 (must not build): property (i) of the normal form is not automatic

For the diagonal matrix `C72T6O5.Tests.diagM` with entries `1 + t², 1, …, 1`, the row at depth 0 has key 2 and the
other rows have key 1, so property (i) (`C72T6O5.NFi`) fails. Positive side: `C72T6O5.Tests.not_NFi_diagM`.
Expected failure: the kernel does not reduce the `Decidable` instance to `true`.
-/

open C72.T6O5 C72.T6O5.Tests

theorem C72.ControlsT6O5.c06_property_one : NFi diagM := by
  decide +kernel
