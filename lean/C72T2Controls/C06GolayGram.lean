import C72T2.Golay

/-!
# Control C06 (must not build): the Gram check of the generators is not vacuous

`Three.g24gen_orth` checks that the 12 generators of `G24` are pairwise orthogonal. With one bit of the first
generator changed (bit 1 added: `8391797 + 2`), the same check must fail (the first row then has odd weight).
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three

/-- The masks of `G24` with bit 1 added to the first one. -/
def C72.ControlsT2.badMask : Fin 12 → ℕ :=
  ![8391799, 8394986, 8401364, 8414120, 8439632, 8490656, 8592704, 8796800, 9204992, 10021376, 11654144,
    14919680]

theorem C72.ControlsT2.c06_golay_gram :
    ∀ i j : Fin 12, toVec (C72.ControlsT2.badMask i) ⬝ᵥ toVec (C72.ControlsT2.badMask j) = 0 := by
  decide
