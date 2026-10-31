import C72T4.Main

/-!
# T4 tests on small examples

* The pair model: `(u | v) a = (v | u)` for `a = aStd`, on concrete words.
* Lemma 3.3 (a) on a concrete word.
* Definition 3.1 on the repetition code `{00, 11}` with the zero form.
* The data: the first row of `Y_0` (first line of the archive list) has weight 8.
* T1's labelling and T4's orbit count agree: the standard fixed-point-free involution `stdPerm 36 2 0` of `Fin 72`
  (pairs `{2k, 2k+1}`) has order 2, no fixed point, and 36 orbits.
-/

namespace C72.T4.Tests

open C72 C72.T4 Module Finset Equiv

/-- `(u | v) a = (v | u)`. -/
theorem aStd_swaps_halves :
    permute aStd (pv (![1, 0] : Fin 2 → ZMod 2) ![0, 1]) = pv ![0, 1] ![1, 0] := by
  decide

/-- Lemma 3.3 (a): `|(z | z + y)| = |y| + 2 |z ∖ supp y|`, here `2 + 2 · 1`. -/
theorem wt_pv_add_example :
    wt (pv (![1, 0, 0] : Fin 3 → ZMod 2) (![1, 0, 0] + ![0, 1, 1])) = 4 := by
  decide

/-- Definition 3.1: for `Y = {00, 11}` and `B = 0`, the word `(00 | 11)` lies in `C_B`. -/
theorem CB_rep2_example :
    pv (0 : Fin 2 → ZMod 2) ![1, 1] ∈ CB C72.Tests.rep2 (0 : LinearMap.BilinForm (ZMod 2) C72.Tests.rep2) := by
  refine mem_CB.2 ⟨⟨![1, 1], Submodule.subset_span rfl⟩, 0, fun y' => ?_, ?_⟩
  · simp
  · rw [zero_add]

/-- The first row of `Y_0` has weight 8. -/
theorem wt_row_0_0 : wt (row 0 0) = 8 := by
  decide

theorem stdPerm_36_2_0_sq : (stdPerm (n := 72) 36 2 0 rfl) ^ 2 = 1 := by
  decide +kernel

theorem stdPerm_36_2_0_ne_one : stdPerm (n := 72) 36 2 0 rfl ≠ 1 := by
  decide +kernel

theorem orderOf_stdPerm_36_2_0 : orderOf (stdPerm (n := 72) 36 2 0 rfl) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime stdPerm_36_2_0_sq stdPerm_36_2_0_ne_one

theorem stdPerm_36_2_0_fpf : ∀ i : Fin 72, stdPerm (n := 72) 36 2 0 rfl i ≠ i := by
  decide +kernel

/-- The standard fixed-point-free involution of `Fin 72` has 36 orbits. -/
theorem card_orbits_stdPerm : Fintype.card (Orbits (stdPerm (n := 72) 36 2 0 rfl)) = 36 :=
  card_orbits orderOf_stdPerm_36_2_0 stdPerm_36_2_0_fpf

end C72.T4.Tests
