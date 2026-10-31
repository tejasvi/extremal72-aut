import C72T3.Tests

/-!
# Control C08 (must not build): at threshold 16 the set `R` is a real restriction

The seven depth-0 rows of Table 1 lie in `R` (`C72.T3.Tests.keyRow_mem_R`). The unit row `(1, …, 1)` (pattern
`1111111`, `⟨u, u⟩ = 7 · 1 = 1`) does not: `M(u) = 8 < 16 − |ψ(1)| = 12`.
Expected failure: `decide` proves that the proposition of the theorem below is false (the exact message is in
`controls_expected.txt`).
-/

open C72.T3

theorem C72.T3.Controls.c08_all_ones_row_in_R : 16 ≤ M (fun _ : Fin 7 => (1 : F16)) + wpsi 1 := by
  decide +kernel
