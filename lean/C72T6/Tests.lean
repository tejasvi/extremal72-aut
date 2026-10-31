import C72T6.Toy

/-!
# T6: tests

* The converse lemmas apply: for `Y4` and `B4 ∈ A_0(Y4)` (`C72T6/Toy.lean`), `C_{B4}` is a doubly-even self-dual code of
  length 8 with the automorphism `aStd` and contracted fixed code `Y4` (`test_converse_Y4`).
* Lemma 6.1 (b) on `Y4`: `D_T(1100, 0011) = 0` for every `T` (`test_disjoint_Y4`).
* `G_0(Y_k)` has an echelon basis for every `k` (`test_echelon_Yc`), so `H_D_of_slice` and `lemma63_order2` apply.
* Keys and bits on numbers (`test_key_head`, `test_key_first_diff`, `test_leading_bits`).
-/

namespace C72.T6.Tests

open C72 C72.T4 C72.T6 C72.T6.Toy

theorem test_converse_Y4 : SelfDual (CB Y4 B4) ∧ (∀ c ∈ CB Y4 B4, 4 ∣ wt c) ∧
    (∀ c ∈ CB Y4 B4, permute aStd c ∈ CB Y4 B4) ∧ Yof (CB Y4 B4) = Y4 :=
  ⟨CB_selfDual Y4_selfDual B4 B4_InA0.1, CB_doublyEven Y4_selfDual allOnes_mem_Y4 B4 B4_InA0.2,
    aStd_mem_CB Y4_selfDual B4, Yof_CB Y4_selfDual B4⟩

theorem test_disjoint_Y4 (T : Finset (Fin 4)) :
    DT Y4 T ⟨![1, 1, 0, 0], mem_Y4.2 ⟨rfl, rfl⟩⟩ ⟨![0, 0, 1, 1], mem_Y4.2 ⟨rfl, rfl⟩⟩ = 0 :=
  G0_apply_disjoint _ (Submodule.subset_span ⟨T, rfl⟩) _ _ (by decide)

theorem test_echelon_Yc (k : Fin 41) :
    ∃ m, Nonempty (EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) :=
  exists_echelonBasis_G0 (Yc k)

theorem test_key_head : toLex (![1, 7] : Fin 2 → ℕ) < toLex ![2, 0] :=
  key_lt_of_head_lt _ _ (by decide)

theorem test_key_first_diff : toLex (![1, 3, 9] : Fin 3 → ℕ) < toLex ![1, 4, 0] :=
  key_lt_of_first_diff _ _ 1 (by decide) (by decide)

theorem test_leading_bits : (9 : ℕ) < 12 :=
  lt_of_leading_bits_lt 9 12 2 (by decide)

end C72.T6.Tests
