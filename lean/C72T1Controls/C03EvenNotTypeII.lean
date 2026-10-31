import C72T1.Tests

/-!
# Control C03 (must not build): Type II means doubly-even, not even

The repetition code `rep2 = {00, 11}` is self-dual (`C72.Tests.rep2_selfDual`) and even
(`C72.Tests.rep2_even`), but `11` has weight 2. The same proof that shows `e8` is Type II must fail here.
Expected failure: `decide` proves that `∀ a, 4 ∣ wt (a • ![1, 1])` is false.
-/

open C72 C72.Tests

theorem C72.Controls.c03_even_not_typeII : TypeII rep2 := by
  refine ⟨rep2_selfDual, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  clear hx
  revert a
  decide
