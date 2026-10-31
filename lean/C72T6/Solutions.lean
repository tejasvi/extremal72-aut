import C72T6.Converse
import C72T6.Search
import C72T4.Main

/-!
# T6: the paper's bad sets, Lemma 3.6 in both directions, and Proposition 6.2

The paper defines `Bad(y)` with the pattern sizes `E_8 = {0, 2}`, `E_10 = {1}`, `E_12 = {0}`; the programs (and `H_D`,
`RuledOut`) use every size with `2|e| < 16 - |y|`. For `B ∈ A_0` both give the same condition, because a matching pattern
`e` gives a word of `C_B` of weight `|y| + 2|e|`, and this weight is divisible by 4 (Sections 3.6 and 6.2):
`ruledOut_iff_ruledOutE`. Hence the programs' solutions are the paper's solutions (`isSol_iff_isSolE`), and `H_D k` says
that no form of `A_0(Y_k)` meets the paper's conditions (`H_D_iff_E`).

* **Lemma 3.6** for `B ∈ A_0` (`lemma36_iff`): if `Y` is self-dual with minimum weight at least 8, then `C_B` has minimum
  weight at least 16 if and only if `s_y(B) ∉ Bad(y)` for every word `y` of weight 8, 10 or 12.
* **Proposition 6.2**, forward (`prop62_forward`, `prop62_forward_slice`): an extremal code with a fixed-point-free
  involution whose contracted fixed code is equivalent to `Y_k` is equivalent to `C_B` for a form `B ∈ A_0(Y_k)` that is not
  ruled out, and the form of the slice in `B + G_0` is a solution. Backward with the paper's conditions:
  `prop62_converse_E`.
-/

namespace C72.T6

open C72 C72.T4 Module Finset Equiv

/-- The paper's pattern sizes `E_8 = {0, 2}`, `E_10 = {1}`, `E_12 = {0}` (Section 3.4). -/
def Eset (w : ℕ) : Finset ℕ :=
  if w = 8 then {0, 2} else if w = 10 then {1} else if w = 12 then {0} else ∅

theorem two_mul_lt_of_mem_Eset {w c : ℕ} (hw : w = 8 ∨ w = 10 ∨ w = 12) (hc : c ∈ Eset w) : 2 * c < 16 - w := by
  rcases hw with rfl | rfl | rfl <;> simp [Eset] at hc <;> omega

theorem mem_Eset_of {w c : ℕ} (hw : w = 8 ∨ w = 10 ∨ w = 12) (hlt : 2 * c < 16 - w) (h4 : 4 ∣ w + 2 * c) :
    c ∈ Eset w := by
  rcases hw with rfl | rfl | rfl <;> simp [Eset] <;> omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Submodule (ZMod 2) (ι → ZMod 2))

/-- The paper's condition `s_y(B) ∈ Bad(y)`: a set `e` outside `supp y` with `|e| ∈ E_{|y|}` matches the syndrome of `B`
at `y`. -/
def BadAtE (B : LinearMap.BilinForm (ZMod 2) Y) (y : Y) : Prop :=
  ∃ e : Finset ι, (∀ i ∈ e, (y : ι → ZMod 2) i = 0) ∧ e.card ∈ Eset (wt (y : ι → ZMod 2)) ∧
    ∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) → indicator e ⬝ᵥ (x : ι → ZMod 2) = B y x

/-- Some constraint word has its syndrome in the paper's `Bad(y)`. -/
def RuledOutE (B : LinearMap.BilinForm (ZMod 2) Y) : Prop :=
  ∃ y : Y, IsConstraint (y : ι → ZMod 2) ∧ BadAtE Y B y

variable {Y}

theorem badAt_of_badAtE {B : LinearMap.BilinForm (ZMod 2) Y} {y : Y} (hy : IsConstraint (y : ι → ZMod 2))
    (h : BadAtE Y B y) : BadAt Y B y := by
  obtain ⟨e, he, hc, hsyn⟩ := h
  exact ⟨e, he, two_mul_lt_of_mem_Eset hy hc, hsyn⟩

/-- For `B ∈ A_0`, a pattern of the programs that matches the syndrome at a constraint word has a size in `E_{|y|}`. -/
theorem badAtE_of_badAt (hY : SelfDual Y) {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hA : InA0 Y h1 B) {y : Y} (hy : IsConstraint (y : ι → ZMod 2)) (h : BadAt Y B y) : BadAtE Y B y := by
  obtain ⟨e, he, hlt, hsyn⟩ := h
  obtain ⟨c, hc, hwc, -⟩ := lemma36 hY B y e he hsyn
  have h4 := CB_doublyEven hY h1 B hA.2 c hc
  rw [hwc] at h4
  exact ⟨e, he, mem_Eset_of hy hlt h4, hsyn⟩

/-- For `B ∈ A_0` the programs' condition and the paper's condition agree. -/
theorem ruledOut_iff_ruledOutE (hY : SelfDual Y) {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hA : InA0 Y h1 B) : RuledOut Y B ↔ RuledOutE Y B :=
  ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, badAtE_of_badAt hY hA hy h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, badAt_of_badAtE hy h⟩⟩

/-- **Lemma 3.6** for `B ∈ A_0`: if `Y` is self-dual with minimum weight at least 8, then `C_B` has minimum weight at least
16 if and only if no word of weight 8, 10 or 12 has its syndrome in the paper's `Bad(y)`. -/
theorem lemma36_iff (hY : SelfDual Y) (h8 : MinWt Y 8) {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hA : InA0 Y h1 B) : MinWt (CB Y B) 16 ↔ ¬ RuledOutE Y B := by
  constructor
  · rintro hmin ⟨y, hy, e, he, hc, hsyn⟩
    obtain ⟨c, hcC, hwc, hc0⟩ := lemma36 hY B y e he hsyn
    have hy0 : (y : ι → ZMod 2) ≠ 0 := by
      intro h0
      unfold IsConstraint at hy
      rw [h0, wt, hammingNorm_zero] at hy
      omega
    have h16 := hmin c hcC (hc0 hy0)
    have hlt := two_mul_lt_of_mem_Eset hy hc
    unfold IsConstraint at hy
    omega
  · intro hnr
    exact minWt_CB hY h8 h1 B hA (fun h => hnr ((ruledOut_iff_ruledOutE hY hA).1 h))

/-- The paper's solutions for `Y_k` (Section 6.1): forms of `S_0` with `s_y(B) ∉ Bad(y)` for every constraint word. -/
def IsSolE (k : Fin 41) {m : ℕ} (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m)
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : Prop :=
  InA0 (Yc k) (allOnes_mem_Yc k) B ∧ B ∈ slice E ∧ ¬ RuledOutE (Yc k) B

/-- The programs' solutions are the paper's solutions. -/
theorem isSol_iff_isSolE (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m)
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : IsSol k E B ↔ IsSolE k E B :=
  ⟨fun ⟨hA, hs, hnr⟩ => ⟨hA, hs, fun h => hnr ((ruledOut_iff_ruledOutE (Yc_selfDual k) hA).2 h)⟩,
    fun ⟨hA, hs, hnr⟩ => ⟨hA, hs, fun h => hnr ((ruledOut_iff_ruledOutE (Yc_selfDual k) hA).1 h)⟩⟩

/-- `H_D k` with the paper's conditions. -/
theorem H_D_iff_E (k : Fin 41) : H_D k ↔ ∀ B, InA0 (Yc k) (allOnes_mem_Yc k) B → RuledOutE (Yc k) B := by
  rw [H_D_iff]
  exact forall_congr' fun B => imp_congr_right fun hA => ruledOut_iff_ruledOutE (Yc_selfDual k) hA

/-- **Proposition 6.2, forward.** An extremal code with a fixed-point-free involution `a` whose contracted fixed code is
equivalent to `Y_k` is equivalent to `C_B` for a form `B ∈ A_0(Y_k)` that is not ruled out. -/
theorem prop62_forward (k : Fin 41) {C : Code 72} (hC : Ext72 C) {a : Perm (Fin 72)} (ha : a ∈ Aut C)
    (hord : orderOf a = 2) (hfp : ∀ i, a i ≠ i) (hequiv : CodeEquiv (contracted a C) (Yc k)) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Yc k), InA0 (Yc k) (allOnes_mem_Yc k) B ∧ ¬ RuledOut (Yc k) B ∧
      CodeEquiv C (CB (Yc k) B) := by
  obtain ⟨ψ, hψ⟩ := hequiv
  have ha2 := mul_self_eq_one_of_orderOf_two hord
  have hY : Yof (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) = Yc k := by
    rw [Yof_map_pairEquiv]
    exact hψ
  have hT : TypeII (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) := TypeII.map_reindex hC.1 _
  have hM : MinWt (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) 16 := MinWt.map_reindex hC.2.1 _
  have hinv : ∀ c ∈ C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap,
      permute aStd c ∈ C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap := by
    rintro _ ⟨c, hc, rfl⟩
    show permute aStd (reindex (pairEquiv ha2 hfp ψ) c) ∈ _
    rw [permute_aStd_reindex]
    exact Submodule.mem_map_of_mem (permute_mem_of_mem_Aut ha hc)
  obtain ⟨B, hCB, hsym, hdiag⟩ := model hY hT hinv (Yc_selfDual k)
  refine ⟨B, ⟨hsym, hdiag⟩, ?_, ⟨pairEquiv ha2 hfp ψ, hCB.symm⟩⟩
  rintro ⟨y, hwy, e, he, hcard, hsyn⟩
  obtain ⟨c, hcmem, hcwt, hcne⟩ := lemma36 (Yc_selfDual k) B y e he hsyn
  rw [hCB] at hcmem
  unfold IsConstraint at hwy
  have hy0 : (y : Fin 36 → ZMod 2) ≠ 0 := by
    intro h0
    rw [h0, wt, hammingNorm_zero] at hwy
    omega
  have h16 := hM c hcmem (hcne hy0)
  omega

/-- **Proposition 6.2, forward, on the slice.** In the situation of `prop62_forward`, the form of the slice in `B + G_0`
is a solution in the paper's sense, for every echelon basis of `G_0(Y_k)`. -/
theorem prop62_forward_slice (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) {C : Code 72} (hC : Ext72 C)
    {a : Perm (Fin 72)} (ha : a ∈ Aut C) (hord : orderOf a = 2) (hfp : ∀ i, a i ≠ i)
    (hequiv : CodeEquiv (contracted a C) (Yc k)) : ∃ B, IsSolE k E B := by
  obtain ⟨B, hA, hnr, -⟩ := prop62_forward k hC ha hord hfp hequiv
  have hD := sliceRep_sub_mem E B
  have hrep : B + (sliceRep E B - B) = sliceRep E B := by abel
  have hA' : InA0 (Yc k) (allOnes_mem_Yc k) (sliceRep E B) := by
    rw [← hrep]
    exact InA0_add hA hD
  refine ⟨sliceRep E B, (isSol_iff_isSolE k E _).1 ⟨hA', sliceRep_mem_slice E B, ?_⟩⟩
  rw [← hrep, ruledOut_add_iff _ hD]
  exact hnr

/-- **Proposition 6.2, backward**, with the paper's conditions (see `prop62_converse`). -/
theorem prop62_converse_E (k : Fin 41) (B : LinearMap.BilinForm (ZMod 2) (Yc k))
    (hA : InA0 (Yc k) (allOnes_mem_Yc k) B) (hnr : ¬ RuledOutE (Yc k) B) (h8 : MinWt (Yc k) 8) :
    TypeII (CB (Yc k) B) ∧ MinWt (CB (Yc k) B) 16 ∧ (∀ c ∈ CB (Yc k) B, permute aStd c ∈ CB (Yc k) B) ∧
      Yof (CB (Yc k) B) = Yc k :=
  prop62_converse k B hA (fun h => hnr ((ruledOut_iff_ruledOutE (Yc_selfDual k) hA).1 h)) h8

end C72.T6
