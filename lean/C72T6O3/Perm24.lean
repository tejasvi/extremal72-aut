import C72T2.Golay

/-!
# T6 (order 3): permutations of 24 points given by codes, and a check of membership in `Aut G24`

A permutation of `Fin 24` is given by two natural numbers (`mkPerm c d h`): byte `i` of `c` (least significant
first) is the image of the point `i`, `d` encodes the inverse, and `h : invPair c d = true` checks that the two
maps are inverse to each other (a Bool recursion over the 24 points, sound by `invPair_spec`).

`autOK m` is a Bool check that `m` maps each of the 12 generators of `G24` to a word orthogonal to all 12
generators; since `G24` is self-dual this gives `m ∈ Aut G24` (`mem_Aut_of_autOK`).
-/

namespace C72.Three.M24

open Equiv Finset

/-- Entry `i` of a code with one byte per entry, reduced modulo 24. -/
def dec (c : ℕ) (i : Fin 24) : Fin 24 :=
  ⟨(c >>> (8 * i.val)) % 256 % 24, Nat.mod_lt _ (by decide)⟩

/-- The maps decoded from `c` and `d` are inverse to each other. -/
def invPair (c d : ℕ) : Bool :=
  (List.finRange 24).all fun i => dec d (dec c i) == i && dec c (dec d i) == i

theorem invPair_spec {c d : ℕ} (h : invPair c d = true) :
    (∀ i, dec d (dec c i) = i) ∧ (∀ i, dec c (dec d i) = i) := by
  simp only [invPair, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq] at h
  exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- The permutation with code `c` and inverse code `d`. -/
def mkPerm (c d : ℕ) (h : invPair c d = true) : Perm (Fin 24) where
  toFun := dec c
  invFun := dec d
  left_inv := fun i => (invPair_spec h).1 i
  right_inv := fun i => (invPair_spec h).2 i

theorem mkPerm_apply (c d : ℕ) (h : invPair c d = true) (i : Fin 24) : mkPerm c d h i = dec c i :=
  rfl

theorem mkPerm_symm_apply (c d : ℕ) (h : invPair c d = true) (i : Fin 24) :
    (mkPerm c d h).symm i = dec d i :=
  rfl

/-- Bool check: `m` maps every generator of `G24` to a word orthogonal to every generator. -/
def autOK (m : Perm (Fin 24)) : Bool :=
  (List.finRange 12).all fun s => (List.finRange 12).all fun j =>
    decide (permute m (g24gen s) ⬝ᵥ g24gen j = 0)

/-- Soundness of `autOK`. -/
theorem mem_Aut_of_autOK {m : Perm (Fin 24)} (h : autOK m = true) : m ∈ Aut G24 := by
  simp only [autOK, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  apply mem_Aut_of_map_le
  rw [G24, Submodule.map_span_le]
  rintro _ ⟨s, rfl⟩
  exact mem_G24_of_orth (h s)

end C72.Three.M24
