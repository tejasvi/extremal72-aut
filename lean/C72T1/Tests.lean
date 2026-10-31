import C72T1.Defs
import C72T1.Labelling
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# T1 tests on small examples

* The action convention: `permute p` moves the unit word at `i` to the unit word at `p i`, i.e.
  `(x p)_{p(i)} = x_i`; the code `C p` of a span is the span of the moved generators; the Lean product
  `p * q` acts first by `q`.
* `Aut` on the `[4,2]` code spanned by `1100` and `0011`: `(0 1) ∈ Aut`, `(1 2) ∉ Aut`.
* The numbering of `stdPerm` (labelling lemma) for `(c, p, f) = (2, 3, 1)`, `(14, 5, 2)`, `(24, 3, 0)` and `(36, 2, 0)`.
* The definitions on known small codes: `e8` (the paper's Fano-plane description, Section 2.2) is Type II with
  minimum weight 4 and an automorphism of order 7; the repetition code of length 2 is self-dual and even but
  not doubly-even, so it is not Type II.

Every check is a kernel `decide` or an elementary proof.
-/

namespace C72.Tests

open Equiv Module

/-! ## The action convention -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`. -/
def c3 : Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

theorem c3_values : c3 0 = 1 ∧ c3 1 = 2 ∧ c3 2 = 0 := by
  decide

/-- `(x p)_{p(i)} = x_i`: the unit word at `0` goes to the unit word at `c3 0 = 1`. -/
theorem permute_c3_single : permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 1 1 := by
  decide

/-- The word `(x₀, x₁, x₂) = (1, 1, 0)` goes to `(x₂, x₀, x₁) = (0, 1, 1)`. -/
theorem permute_c3_word : permute c3 (![1, 1, 0] : Fin 3 → ZMod 2) = ![0, 1, 1] := by
  decide

/-- The code spanned by the unit word at `0` is mapped onto the code spanned by the unit word at `1`. -/
theorem map_span_c3 :
    (Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)}).map (permute c3).toLinearMap =
      Submodule.span (ZMod 2) {Pi.single 1 1} := by
  rw [Submodule.map_span, Set.image_singleton]
  congr 2
  exact permute_c3_single

/-- The Lean product `p * q` acts first by `q` (`permute_mul`); here `p * q ≠ q * p` on a unit word. -/
theorem permute_mul_example :
    permute (c3 * Equiv.swap 0 1) (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 2 1 ∧
      permute (Equiv.swap 0 1 * c3) (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1 := by
  decide

/-! ## `Aut` on a small code -/

/-- The `[4,2]` code spanned by `1100` and `0011`. -/
def C4 : Code 4 :=
  Submodule.span (ZMod 2) {![1, 1, 0, 0], ![0, 0, 1, 1]}

theorem swap01_mem_Aut_C4 : Equiv.swap (0 : Fin 4) 1 ∈ Aut C4 := by
  apply mem_Aut_of_map_le
  rw [C4, Submodule.map_span_le]
  intro m hm
  rcases hm with rfl | rfl
  · have h : permute (Equiv.swap (0 : Fin 4) 1) (![1, 1, 0, 0] : Fin 4 → ZMod 2) = ![1, 1, 0, 0] := by
      decide
    show permute (Equiv.swap (0 : Fin 4) 1) (![1, 1, 0, 0] : Fin 4 → ZMod 2) ∈ _
    rw [h]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · have h : permute (Equiv.swap (0 : Fin 4) 1) (![0, 0, 1, 1] : Fin 4 → ZMod 2) = ![0, 0, 1, 1] := by
      decide
    show permute (Equiv.swap (0 : Fin 4) 1) (![0, 0, 1, 1] : Fin 4 → ZMod 2) ∈ _
    rw [h]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

theorem swap12_not_mem_Aut_C4 : Equiv.swap (1 : Fin 4) 2 ∉ Aut C4 := by
  intro h
  have hmem : permute (Equiv.swap (1 : Fin 4) 2) (![1, 1, 0, 0] : Fin 4 → ZMod 2) ∈ C4 :=
    permute_mem_of_mem_Aut h (Submodule.subset_span (Set.mem_insert _ _))
  have hval : permute (Equiv.swap (1 : Fin 4) 2) (![1, 1, 0, 0] : Fin 4 → ZMod 2) = ![1, 0, 1, 0] := by
    decide
  rw [hval, C4, Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  revert a b hab
  decide

/-! ## The numbering of the labelling lemma -/

/-- Two 3-cycles and one fixed point: `0 → 1 → 2 → 0`, `3 → 4 → 5 → 3`, `6` fixed. -/
theorem stdPerm_2_3_1 :
    ∀ i : Fin 7, stdPerm (n := 7) 2 3 1 rfl i = (![1, 2, 0, 4, 5, 3, 6] : Fin 7 → Fin 7) i := by
  decide

/-- The paper's numbering for order 5 (Section 2.1): cycles `{5i, …, 5i+4}`, fixed points 70 and 71. -/
theorem stdPerm_14_5_2 :
    stdPerm (n := 72) 14 5 2 rfl 0 = 1 ∧ stdPerm (n := 72) 14 5 2 rfl 4 = 0 ∧
      stdPerm (n := 72) 14 5 2 rfl 65 = 66 ∧ stdPerm (n := 72) 14 5 2 rfl 69 = 65 ∧
      stdPerm (n := 72) 14 5 2 rfl 70 = 70 ∧ stdPerm (n := 72) 14 5 2 rfl 71 = 71 := by
  decide

/-- Order 3 (Section 4.1): 24 cycles `{3k, 3k+1, 3k+2}` (the paper labels them `(i, j)`, `j ∈ ℤ/3`) and no
fixed point. -/
theorem stdPerm_24_3_0 :
    stdPerm (n := 72) 24 3 0 rfl 0 = 1 ∧ stdPerm (n := 72) 24 3 0 rfl 2 = 0 ∧
      stdPerm (n := 72) 24 3 0 rfl 69 = 70 ∧ stdPerm (n := 72) 24 3 0 rfl 71 = 69 := by
  decide

/-- A fixed-point-free involution (Section 3): 36 pairs `{2k, 2k+1}` (the paper labels them `(i, 0)`, `(i, 1)`). -/
theorem stdPerm_36_2_0 :
    stdPerm (n := 72) 36 2 0 rfl 0 = 1 ∧ stdPerm (n := 72) 36 2 0 rfl 1 = 0 ∧
      stdPerm (n := 72) 36 2 0 rfl 70 = 71 ∧ stdPerm (n := 72) 36 2 0 rfl 71 = 70 := by
  decide

/-! ## The definitions on known codes -/

/-- Generators of `e8`: the words `(L, 1)` for the Fano lines `{0,1,3}`, `{1,2,4}`, `{2,3,5}`, `{3,4,6}`,
with coordinate 7 as the fixed point (Section 2.2 of the paper). -/
def e8gen : Fin 4 → Fin 8 → ZMod 2 :=
  ![![1, 1, 0, 1, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 0, 0, 1], ![0, 0, 1, 1, 0, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0, 1, 1]]

/-- The extended Hamming code `e8`. -/
def e8 : Code 8 :=
  Submodule.span (ZMod 2) (Set.range e8gen)

theorem mem_e8_iff {x : Fin 8 → ZMod 2} :
    x ∈ e8 ↔ ∃ a b c d : ZMod 2, a • e8gen 0 + b • e8gen 1 + c • e8gen 2 + d • e8gen 3 = x := by
  rw [e8, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c 0, c 1, c 2, c 3, by rw [← hc, Fin.sum_univ_four]⟩
  · rintro ⟨a, b, c, d, h⟩
    refine ⟨![a, b, c, d], ?_⟩
    rw [Fin.sum_univ_four]
    exact h

theorem e8gen_linearIndependent : LinearIndependent (ZMod 2) e8gen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  have key : ∀ a b c d : ZMod 2, a • e8gen 0 + b • e8gen 1 + c • e8gen 2 + d • e8gen 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
    decide
  obtain ⟨h0, h1, h2, h3⟩ := key _ _ _ _ hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem finrank_e8 : finrank (ZMod 2) e8 = 4 := by
  rw [e8, finrank_span_eq_card e8gen_linearIndependent, Fintype.card_fin]

theorem e8_le_dual : e8 ≤ dual e8 := by
  rw [e8, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨j, rfl⟩
  revert i j
  decide

theorem e8_selfDual : SelfDual e8 :=
  selfDual_of_le_of_two_mul_finrank e8_le_dual (by rw [finrank_e8, Fintype.card_fin])

theorem e8_typeII : TypeII e8 := by
  refine ⟨e8_selfDual, fun x hx => ?_⟩
  obtain ⟨a, b, c, d, rfl⟩ := mem_e8_iff.1 hx
  clear hx
  revert a b c d
  decide

theorem e8_minWt : MinWt e8 4 := by
  intro x hx
  obtain ⟨a, b, c, d, rfl⟩ := mem_e8_iff.1 hx
  clear hx
  revert a b c d
  decide

theorem e8_has_weight_four : ∃ x ∈ e8, wt x = 4 :=
  ⟨e8gen 0, Submodule.subset_span ⟨0, rfl⟩, by decide⟩

/-- The Fano collineation `i ↦ i + 1 (mod 7)` on coordinates `0, …, 6`, fixing coordinate 7. -/
def sigma7 : Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6

theorem sigma7_values : ∀ i : Fin 8, sigma7 i = (![1, 2, 3, 4, 5, 6, 0, 7] : Fin 8 → Fin 8) i := by
  decide

theorem sigma7_mem_Aut_e8 : sigma7 ∈ Aut e8 := by
  apply mem_Aut_of_map_le
  rw [e8, Submodule.map_span_le]
  rintro _ ⟨i, rfl⟩
  show permute sigma7 (e8gen i) ∈ e8
  rw [mem_e8_iff]
  revert i
  decide

theorem orderOf_sigma7 : orderOf sigma7 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide

/-- `e8` is Type II with minimum weight 4, and `Aut e8` contains an element of order 7, so the predicates
are satisfiable and `Aut C = ⊥` is not automatic. -/
theorem e8_check : TypeII e8 ∧ MinWt e8 4 ∧ (∃ x ∈ e8, wt x = 4) ∧ ∃ g ∈ Aut e8, orderOf g = 7 :=
  ⟨e8_typeII, e8_minWt, e8_has_weight_four, sigma7, sigma7_mem_Aut_e8, orderOf_sigma7⟩

theorem Aut_e8_ne_bot : Aut e8 ≠ ⊥ := by
  intro h
  have hmem := sigma7_mem_Aut_e8
  rw [h, Subgroup.mem_bot] at hmem
  have h7 := orderOf_sigma7
  rw [hmem, orderOf_one] at h7
  exact absurd h7 (by decide)

/-- The repetition code of length 2. -/
def rep2 : Code 2 :=
  Submodule.span (ZMod 2) {![1, 1]}

theorem rep2_selfDual : SelfDual rep2 := by
  refine selfDual_of_le_of_two_mul_finrank ?_ ?_
  · rw [rep2, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_dual_span]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    decide
  · rw [rep2, finrank_span_singleton (by decide), Fintype.card_fin]

/-- `rep2` is even: every weight is divisible by 2. -/
theorem rep2_even : ∀ x ∈ rep2, 2 ∣ wt x := by
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  clear hx
  revert a
  decide

/-- `rep2` is not doubly-even, so it is not Type II (Type II means doubly-even). -/
theorem rep2_not_typeII : ¬ TypeII rep2 := by
  intro h
  have h4 := h.2 ![1, 1] (Submodule.subset_span rfl)
  revert h4
  decide

end C72.Tests
