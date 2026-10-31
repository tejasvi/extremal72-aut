import C72T6O5.Scan

/-!
# Control C04 (must not build): the scan processes row 3 before row 2

The rows are processed in the order `0, 1, 3, 2, 4, 5, 6`, so the first entry of row 2 comes after the first entry
of row 3. Expected failure: `decide` proves the statement false.
-/

open C72.T6O5

theorem C72.ControlsT6O5.c04_scan_order : scanIdx 2 0 < scanIdx 3 0 := by
  decide
