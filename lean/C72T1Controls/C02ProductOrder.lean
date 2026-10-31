import C72T1.Tests

/-!
# Control C02 (must not build): the order of a product

`permute (p * q) = permute p ∘ permute q` (`C72.permute_mul`): the Lean product acts first by `q`. The reversed
reading, `permute (p * q) = permute q ∘ permute p`, is false for `p = c3`, `q = (0 1)` on the unit word at `0`.
Expected failure: `decide` proves that the proposition is false.
-/

open C72 C72.Tests

theorem C72.Controls.c02_product_order :
    permute (c3 * Equiv.swap 0 1) (Pi.single 0 1 : Fin 3 → ZMod 2) =
      permute (Equiv.swap 0 1) (permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2)) := by
  decide
