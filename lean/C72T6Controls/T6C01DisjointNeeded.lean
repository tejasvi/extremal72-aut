import C72T6.Refute

/-!
# Control T6C01 (must not build): Lemma 6.1 (b) needs disjointness

Lemma 6.1 (b) (`C72.T6.G0_apply_disjoint`) gives `D(y, x) = 0` for `D ∈ G_0` and `x` disjoint from `y`. Without
disjointness it fails: `D_{{0}} ∈ G_0(Y4)` and `D_{{0}}(1100, 1100) = 1` (`C72.T6.Refute.lemma61b_needs_disjoint`).
Expected failure: `decide` proves that `D_{{0}}(1100, 1100) = 0` is false.
-/

open C72.T6 C72.T6.Toy C72.T6.Refute

theorem C72.Controls.t6c01_disjoint_needed : DT Y4 {0} u1 u1 = 0 := by
  decide
