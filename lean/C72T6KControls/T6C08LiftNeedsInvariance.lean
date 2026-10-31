import C72T6K.KleinRefute

/-!
# Control T6C08 (must not build): Lemma 3.4 (c) needs a `β`-invariant form

`C72.T6.liftP_mem_Aut_CB_iff`: the lift of `β` is an automorphism of `C_B` if and only if `B^β = B`. For `β = (0 2)(1 3)` on
`Y4` and `Bn(x, x') = x₀x'₂`, `Bn^β(u1, u2) = Bn(u2, u1) = 0` and `Bn(u1, u2) = 1`, so the lift of `β` is not an
automorphism of `C_{Bn}` (`C72.T6.KleinRefute.liftP_needs_invariance`).
Expected failure: `decide` proves that `Bn^β(u1, u2) = Bn(u1, u2)` is false.
-/

open C72.T6 C72.T6.Toy C72.T6.Refute C72.T6.KleinTests

theorem C72.Controls.t6c08_lift_needs_invariance : formAct βT Bn u1 u2 = Bn u1 u2 := by
  decide
