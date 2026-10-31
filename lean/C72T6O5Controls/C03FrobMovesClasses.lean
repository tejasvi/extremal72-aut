import C72T6O5.Key

/-!
# Control C03 (must not build): the Frobenius map moves the norm classes

`C72T6O5.cls_sq` says that `y ↦ y²` fixes class 1 and interchanges classes 2 and 3. So it does not fix every class.
Expected failure: `decide` proves the proposition false.
-/

open C72.T3 C72.T6O5

theorem C72.ControlsT6O5.c03_frob_moves_classes : ∀ y : F16, cls (y ^ 2) = cls y := by
  decide +kernel
