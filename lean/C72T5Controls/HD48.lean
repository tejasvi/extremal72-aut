import C72T5Controls.HD48Check
import C72T4.Hyps
import C72T5.Known

/-!
# T5 controls: the length-48 analog of `H_D` is false

`H_D k` (T4) states the result of the order-2 search for the code `Y_k`: for every form
`B ∈ A_0(Y_k)` some constraint word `y` of weight 8, 10 or 12 has a set `e` of coordinates outside `supp y` with
`2|e| < 16 − |y|` and `⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y_k` disjoint from `y`. By Lemma 3.6 the code `C_B` then has
a nonzero word of weight `|y| + 2|e| < 16`.

This control shows that the analogous statement at length 48 is false, so that the shape of `H_D` does not make it
true for an empty reason. The extended quadratic residue code `C` of length 48 (spanned by the shifts of the
quadratic-residue word modulo 47; the image of the supplement's QR48 under `x ↦ −x`) is an extremal Type II
`[48,24,12]` code with the fixed-point-free involution `x ↦ −1/x` of `P¹(𝔽₄₇)`. Its contracted fixed code `Y48`
(length 24) and its form `B48` (`C = C_B`, T4's Definition 3.1) come from the data of `C72T5Controls.HD48Check`.
`H_D48` is `H_D` with 24 coordinates in place of 36 and the threshold 12 (the minimum weight of an extremal code of
length 48) in place of 16; the weights 8, 10, 12 become 4, 6, 8, with the same bounds on `|e|`. With T4's definitions
(`InA0`, `indicator`) and T1's `wt`:
* `Y48` is self-dual (`Y48_selfDual`) with minimum weight 6 (`Y48_minWt`);
* `B48 ∈ A_0(Y48)` (`B48_inA0`): `B48` is symmetric and satisfies (diag) `B(y, y) = |y|/2 + B(y, 𝟙)`;
* no word `y ≠ 0` of `Y48` of weight below 12 has a bad pattern `e` (`no_bad_pattern`), by the kernel check
  `go_all` and the soundness lemma `go_sound`;
* hence `¬ H_D48` (`not_H_D48`), and `C_B` has minimum weight 12 (`CB_B48_minWt`).
The proofs use only `Y48` and `B48`, not the code of length 48.
-/

namespace C72.T5.HD48

open C72 C72.T4 Finset Module

/-! ## Words of length 24 -/

/-- A bit as an element of `𝔽₂`. -/
def bz (b : Bool) : ZMod 2 :=
  if b then 1 else 0

theorem bz_xor : ∀ x y : Bool, bz (x ^^ y) = bz x + bz y := by
  decide

theorem bz_inj : ∀ x y : Bool, bz x = bz y → x = y := by
  decide

/-- The word of a mask: coordinate `i` is bit `i`. -/
def vec24 (m : ℕ) : Fin 24 → ZMod 2 :=
  fun i => bz (m.testBit i)

theorem vec24_xor (a b : ℕ) : vec24 (a ^^^ b) = vec24 a + vec24 b := by
  funext i
  simp only [vec24, Nat.testBit_xor, Pi.add_apply]
  exact bz_xor _ _

theorem vec24_zero : vec24 0 = 0 := by
  funext i
  simp only [vec24, Nat.zero_testBit, Pi.zero_apply]
  rfl

theorem sum_pc (m : ℕ) : ∀ n : ℕ, (∑ j : Fin n, if m.testBit j then 1 else 0) = pcUpTo m n
  | 0 => by simp [pcUpTo]
  | n + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [sum_pc m n]
    simp only [pcUpTo, Bool.cond_eq_ite]

theorem wt_vec24 (m : ℕ) : wt (vec24 m) = pcUpTo m 24 := by
  rw [Three.wt_eq_sum, ← sum_pc m 24]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [vec24, bz]
  rcases Bool.eq_false_or_eq_true (m.testBit i) with h | h <;> simp [h]

theorem vec24_dotProduct (m m' : ℕ) : vec24 m ⬝ᵥ vec24 m' = bz (parityUpTo (m &&& m') 24) := by
  simp only [bz]
  rw [← sum_bits_eq]
  simp only [dotProduct, vec24, bz]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.testBit_and]
  rcases Bool.eq_false_or_eq_true (m.testBit j) with h | h <;>
    rcases Bool.eq_false_or_eq_true (m'.testBit j) with h' | h' <;> simp [h, h']

theorem indicator_dotProduct_vec24 (e : Finset (Fin 24)) (m : ℕ) :
    indicator e ⬝ᵥ vec24 m = ∑ i ∈ e, bz (m.testBit i) := by
  simp only [dotProduct, indicator, vec24, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem testBit_false_of_vec24 {a : ℕ} {i : Fin 24} (h : vec24 a i = 0) : a.testBit i = false := by
  rcases Bool.eq_false_or_eq_true (a.testBit i) with hb | hb
  · simp [vec24, bz, hb] at h
  · exact hb

theorem disj_of_and_eq_zero {x a : ℕ} (h : x &&& a = 0) (i : Fin 24) : vec24 a i = 0 ∨ vec24 x i = 0 := by
  have hb := congrArg (fun m => m.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff] at hb
  rcases hb with hb | hb
  · right
    simp [vec24, bz, hb]
  · left
    simp [vec24, bz, hb]

/-! ## Packed syndromes and columns -/

theorem testBit_cons_zero (b : Bool) (r : ℕ) : ((bif b then 1 else 0) + 2 * r).testBit 0 = b := by
  rw [Nat.testBit_zero]
  cases b
  · simp only [Bool.cond_false, zero_add, Nat.mul_mod_right, decide_eq_false_iff_not]
    omega
  · simp only [Bool.cond_true, decide_eq_true_eq]
    omega

theorem testBit_cons_succ (b : Bool) (r k : ℕ) : ((bif b then 1 else 0) + 2 * r).testBit (k + 1) = r.testBit k := by
  rw [Nat.testBit_succ]
  congr 1
  cases b
  · simp only [Bool.cond_false]
    omega
  · simp only [Bool.cond_true]
    omega

theorem testBit_colOf (i : ℕ) : ∀ (xs : List ℕ) (k : ℕ), (colOf i xs).testBit k = (xs.getD k 0).testBit i
  | [], k => by simp [colOf]
  | x :: xs, 0 => by simp only [colOf, testBit_cons_zero, List.getD_cons_zero]
  | x :: xs, k + 1 => by simp only [colOf, testBit_cons_succ, List.getD_cons_succ, testBit_colOf i xs k]

theorem parityUpTo_zero : ∀ n, parityUpTo 0 n = false
  | 0 => rfl
  | n + 1 => by simp [parityUpTo, parityUpTo_zero n]

theorem testBit_svOf (z : ℕ) :
    ∀ (xs : List ℕ) (k : ℕ), (svOf z xs).testBit k = parityUpTo (z &&& xs.getD k 0) 24
  | [], k => by simp [svOf, parityUpTo_zero]
  | x :: xs, 0 => by simp only [svOf, testBit_cons_zero, List.getD_cons_zero]
  | x :: xs, k + 1 => by simp only [svOf, testBit_cons_succ, List.getD_cons_succ, testBit_svOf z xs k]

theorem getD_mem_or_zero (xs : List ℕ) (k : ℕ) : xs.getD k 0 ∈ xs ∨ xs.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < xs.length
  · left
    rw [List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  · right
    rw [List.getElem?_eq_none (by omega), Option.getD_none]

/-- **Soundness of `noE`:** if a set `e` of at most `L` coordinates `i < n` outside `supp y` satisfies
`acc + Σ_{i ∈ e} col i = s` bit by bit, then `noE` returns `false`. -/
theorem noE_false {y s : ℕ} {col : ℕ → ℕ} : ∀ (n L acc : ℕ) (e : Finset (Fin 24)),
    (∀ i ∈ e, i.val < n ∧ y.testBit i.val = false) → e.card ≤ L →
    (∀ k, bz (acc.testBit k) + ∑ i ∈ e, bz ((col i.val).testBit k) = bz (s.testBit k)) →
    noE y s col n L acc = false := by
  have base : ∀ (acc : ℕ) (e : Finset (Fin 24)), e = ∅ →
      (∀ k, bz (acc.testBit k) + ∑ i ∈ e, bz ((col i.val).testBit k) = bz (s.testBit k)) → acc = s := by
    intro acc e he0 hs
    subst he0
    apply Nat.eq_of_testBit_eq
    intro k
    have h := hs k
    rw [Finset.sum_empty, add_zero] at h
    exact bz_inj _ _ h
  intro n
  induction n with
  | zero =>
    intro L acc e he _ hs
    have he0 : e = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => absurd (he i hi).1 (Nat.not_lt_zero _)
    have hacc := base acc e he0 hs
    cases L <;> simp [noE, hacc]
  | succ n ih =>
    intro L acc e he hcard hs
    by_cases hn : ∃ i ∈ e, i.val = n
    · obtain ⟨i0, hi0, hi0n⟩ := hn
      have hyn : y.testBit n = false := by
        rw [← hi0n]
        exact (he i0 hi0).2
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by have := Finset.card_pos.2 ⟨i0, hi0⟩; omega⟩
      have key : noE y s col n L' (acc ^^^ col n) = false := by
        refine ih L' (acc ^^^ col n) (e.erase i0) (fun i hi => ?_) ?_ (fun k => ?_)
        · obtain ⟨hne, hie⟩ := Finset.mem_erase.1 hi
          have h1 := (he i hie).1
          have h2 : i.val ≠ n := fun h => hne (Fin.ext (h.trans hi0n.symm))
          exact ⟨by omega, (he i hie).2⟩
        · rw [Finset.card_erase_of_mem hi0]
          omega
        · rw [Nat.testBit_xor, bz_xor, add_assoc, ← hi0n,
            Finset.add_sum_erase e (fun i => bz ((col i.val).testBit k)) hi0]
          exact hs k
      simp only [noE, hyn, key, Bool.false_or, Bool.and_false]
    · have he' : ∀ i ∈ e, i.val < n ∧ y.testBit i.val = false := by
        intro i hi
        have h1 := (he i hi).1
        have h2 : i.val ≠ n := fun h => hn ⟨i, hi, h⟩
        exact ⟨by omega, (he i hi).2⟩
      cases L with
      | zero =>
        have he0 : e = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
        have hacc := base acc e he0 hs
        simp [noE, hacc]
      | succ L' =>
        have key := ih (L' + 1) acc e he' hcard hs
        simp only [noE, key, Bool.false_and]

/-! ## The code `Y48` and the form `B48` -/

/-- The basis rows of `Y48`. -/
def rowY (j : Fin 12) : Fin 24 → ZMod 2 :=
  vec24 (yrow j)

/-- The words `z_j`. -/
def zvec (j : Fin 12) : Fin 24 → ZMod 2 :=
  vec24 (zrow j)

/-- The contracted fixed code `Y48` of the extended quadratic residue code `C` of length 48 (module docstring) under
`x ↦ −1/x`: the span of the rows `rowY`. -/
def Y48 : Code 24 :=
  Submodule.span (ZMod 2) (Set.range rowY)

/-- The information coordinate `12 + j`. -/
def info (j : Fin 12) : Fin 24 :=
  ⟨j.val + 12, by omega⟩

theorem rowY_info : ∀ j j' : Fin 12, rowY j (info j') = if j = j' then 1 else 0 := by
  decide +kernel

theorem rowY_linearIndependent : LinearIndependent (ZMod 2) rowY := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (info i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowY_info, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at h
  exact h

theorem finrank_Y48 : finrank (ZMod 2) Y48 = 12 := by
  rw [Y48, finrank_span_eq_card rowY_linearIndependent, Fintype.card_fin]

theorem rowY_dotProduct : ∀ j k : Fin 12, rowY j ⬝ᵥ rowY k = 0 := by
  intro j k
  rw [rowY, rowY, vec24_dotProduct]
  revert j k
  decide +kernel

theorem Y48_le_dual : Y48 ≤ dual Y48 := by
  rw [Y48, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨k, rfl⟩
  exact rowY_dotProduct j k

/-- `Y48` is self-dual (a `[24,12]` code; its minimum weight is 6, `Y48_minWt`). -/
theorem Y48_selfDual : SelfDual Y48 :=
  selfDual_of_le_of_two_mul_finrank Y48_le_dual (by rw [finrank_Y48, Fintype.card_fin])

theorem allOnes_mem_Y48 : allOnes ∈ Y48 :=
  allOnes_mem_of_selfDual Y48_selfDual

/-- `y ↦ z_y = Σ_j y_{12+j} z_j`; for `y ∈ Y48` the word `(z_y | z_y + y)` lies in the code of length 48. -/
def Zlin : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun v := ∑ j, v (info j) • zvec j
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem Zlin_apply (v : Fin 24 → ZMod 2) : Zlin v = ∑ j, v (info j) • zvec j :=
  rfl

theorem Zlin_rowY (j : Fin 12) : Zlin (rowY j) = zvec j := by
  rw [Zlin_apply]
  simp only [rowY_info, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The form `B48(y, x) = ⟨z_y, x⟩` on `Y48` (T4's Definition 3.1 for the code of length 48). -/
def B48 : LinearMap.BilinForm (ZMod 2) Y48 :=
  LinearMap.mk₂ (ZMod 2) (fun y x => Zlin y ⬝ᵥ (x : Fin 24 → ZMod 2))
    (fun y₁ y₂ x => by rw [Submodule.coe_add, map_add, add_dotProduct])
    (fun c y x => by rw [Submodule.coe_smul, map_smul, smul_dotProduct])
    (fun y x₁ x₂ => by rw [Submodule.coe_add, dotProduct_add])
    (fun c y x => by rw [Submodule.coe_smul, dotProduct_smul])

theorem B48_apply (y x : Y48) : B48 y x = Zlin y ⬝ᵥ (x : Fin 24 → ZMod 2) :=
  rfl

theorem zvec_rowY_symm : ∀ j k : Fin 12, zvec j ⬝ᵥ rowY k = zvec k ⬝ᵥ rowY j := by
  intro j k
  rw [zvec, zvec, rowY, rowY, vec24_dotProduct, vec24_dotProduct]
  revert j k
  decide +kernel

theorem Zlin_symm {v w : Fin 24 → ZMod 2} (hv : v ∈ Y48) (hw : w ∈ Y48) : Zlin v ⬝ᵥ w = Zlin w ⬝ᵥ v := by
  rw [Y48] at hv hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨k, rfl⟩ := hx'
      rw [Zlin_rowY, Zlin_rowY]
      exact zvec_rowY_symm j k
    | zero => rw [dotProduct_zero, map_zero, zero_dotProduct]
    | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, map_add, add_dotProduct]
    | smul c a _ ha => rw [dotProduct_smul, ha, map_smul, smul_dotProduct]
  | zero => rw [map_zero, zero_dotProduct, dotProduct_zero]
  | add a b _ _ ha hb => rw [map_add, add_dotProduct, ha, hb, dotProduct_add]
  | smul c a _ ha => rw [map_smul, smul_dotProduct, ha, dotProduct_smul]

theorem allOnes_eq_vec24 : (allOnes : Fin 24 → ZMod 2) = vec24 16777215 := by
  funext i
  revert i
  decide +kernel

theorem zvec_diag : ∀ j : Fin 12,
    zvec j ⬝ᵥ rowY j = ((wt (rowY j) / 2 : ℕ) : ZMod 2) + zvec j ⬝ᵥ allOnes := by
  intro j
  rw [allOnes_eq_vec24, zvec, rowY, wt_vec24, vec24_dotProduct, vec24_dotProduct]
  revert j
  decide +kernel

theorem zmod2_diag_add : ∀ p q r s t : ZMod 2, p + q + r + (r + (s + t)) = p + s + (q + t) := by
  decide

theorem Zlin_diag {v : Fin 24 → ZMod 2} (hv : v ∈ Y48) :
    Zlin v ⬝ᵥ v = ((wt v / 2 : ℕ) : ZMod 2) + Zlin v ⬝ᵥ allOnes := by
  rw [Y48] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [Zlin_rowY]
    exact zvec_diag j
  | zero =>
    rw [map_zero, zero_dotProduct, zero_dotProduct, Three.wt_zero, Nat.zero_div, Nat.cast_zero, add_zero]
  | add a b ha hb iha ihb =>
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, iha, ihb, half_wt_add Y48_selfDual ha hb,
      Zlin_symm hb ha, add_dotProduct]
    exact zmod2_diag_add _ _ _ _ _
  | smul c a _ iha =>
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, map_zero, zero_dotProduct, zero_dotProduct, Three.wt_zero, Nat.zero_div, Nat.cast_zero,
        add_zero]
    · rw [one_smul]
      exact iha

/-- `B48 ∈ A_0(Y48)`: symmetric, and (diag) `B(y, y) = |y|/2 + B(y, 𝟙)` for every `y ∈ Y48`. -/
theorem B48_inA0 : InA0 Y48 allOnes_mem_Y48 B48 :=
  ⟨fun y y' => Zlin_symm y.2 y'.2, fun y => Zlin_diag y.2⟩

/-! ## The statement -/

/-- **The length-48 analog of `H_D`**, for the contracted fixed code `Y48` of the extended quadratic residue
code `C` of length 48 (module docstring): T4's `H_D k` with 24 coordinates instead of 36 and the threshold 12 instead
of 16. For every form `B ∈ A_0(Y48)` there is a constraint word `y ∈ Y48` of weight 4, 6 or 8 and a set `e` of
coordinates outside `supp y` with `2|e| < 12 - |y|` such that `⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y48` disjoint
from `y`. -/
def H_D48 : Prop :=
  ∀ B : LinearMap.BilinForm (ZMod 2) Y48, InA0 Y48 allOnes_mem_Y48 B →
    ∃ y : Y48, (wt (y : Fin 24 → ZMod 2) = 4 ∨ wt (y : Fin 24 → ZMod 2) = 6 ∨ wt (y : Fin 24 → ZMod 2) = 8) ∧
      ∃ e : Finset (Fin 24), (∀ i ∈ e, (y : Fin 24 → ZMod 2) i = 0) ∧ 2 * e.card < 12 - wt (y : Fin 24 → ZMod 2) ∧
        ∀ x : Y48, (∀ i, (y : Fin 24 → ZMod 2) i = 0 ∨ (x : Fin 24 → ZMod 2) i = 0) →
          indicator e ⬝ᵥ (x : Fin 24 → ZMod 2) = B y x

/-! ## Soundness of the check -/

/-- The property checked at a leaf of `go T`, for the word `y` with `z`. -/
def LeafProp (T : ℕ) (y z : Fin 24 → ZMod 2) : Prop :=
  y = 0 ∨ (6 ≤ wt y ∧ (wt y < T → ∀ e : Finset (Fin 24), (∀ i ∈ e, y i = 0) → 2 * e.card < T - wt y →
    ∃ x ∈ Y48, (∀ i, y i = 0 ∨ x i = 0) ∧ indicator e ⬝ᵥ x ≠ z ⬝ᵥ x))

theorem yrows_mem : ∀ p ∈ yrows, vec24 p ∈ Y48 := by
  intro p hp
  obtain ⟨j, rfl⟩ : ∃ j : Fin 12, yrow j = p := by
    revert p
    decide +kernel
  exact Submodule.subset_span ⟨j, rfl⟩

theorem mem_elimCol (i : ℕ) : ∀ {ps : List ℕ}, (∀ p ∈ ps, vec24 p ∈ Y48) → ∀ x ∈ elimCol i ps, vec24 x ∈ Y48
  | [], _, x, hx => by simp [elimCol] at hx
  | p :: ps, h, x, hx => by
    have hp : vec24 p ∈ Y48 := h p (by simp)
    have hps : ∀ q ∈ ps, vec24 q ∈ Y48 := fun q hq => h q (by simp [hq])
    simp only [elimCol] at hx
    split_ifs at hx with hpi
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      split_ifs with hqi
      · rw [vec24_xor]
        exact add_mem (hps q hq) hp
      · exact hps q hq
    · rcases List.mem_cons.1 hx with rfl | hx'
      · exact hp
      · exact mem_elimCol i hps x hx'

theorem mem_elim (y : ℕ) : ∀ (n : ℕ) {ps : List ℕ}, (∀ p ∈ ps, vec24 p ∈ Y48) → ∀ x ∈ elim y n ps, vec24 x ∈ Y48
  | 0, _, h => h
  | n + 1, ps, h => by
    show ∀ x ∈ elim y n (if y.testBit n then elimCol n ps else ps), vec24 x ∈ Y48
    apply mem_elim y n
    split_ifs
    · exact mem_elimCol n h
    · exact h

theorem leaf_sound {T a b : ℕ} (h : leafOK T a b = true) : LeafProp T (vec24 a) (vec24 b) := by
  simp only [leafOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.ble_eq] at h
  rw [← wt_vec24] at h
  rcases h with h0 | ⟨h6, hT | hcore⟩
  · left
    exact Three.wt_eq_zero.1 h0
  · right
    exact ⟨h6, fun hw => absurd hT (by omega)⟩
  · right
    refine ⟨h6, fun hw e he hcard => ?_⟩
    simp only [leafCore, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcore
    obtain ⟨hdisj, hnoE⟩ := hcore
    by_contra hall
    have hall' : ∀ x ∈ Y48, (∀ i, vec24 a i = 0 ∨ x i = 0) → indicator e ⬝ᵥ x = vec24 b ⬝ᵥ x :=
      fun x hx hd => by_contra fun hne => hall ⟨x, hx, hd, hne⟩
    have hbits : ∀ k, bz ((0 : ℕ).testBit k) + ∑ i ∈ e, bz ((colOf i.val (elim a 24 yrows)).testBit k) =
        bz ((svOf b (elim a 24 yrows)).testBit k) := by
      intro k
      simp only [Nat.zero_testBit, testBit_colOf, testBit_svOf]
      rcases getD_mem_or_zero (elim a 24 yrows) k with hk | hk
      · have heq := hall' _ (mem_elim a 24 yrows_mem _ hk) (disj_of_and_eq_zero (hdisj _ hk))
        rw [indicator_dotProduct_vec24, vec24_dotProduct] at heq
        rw [heq]
        simp [bz]
      · rw [hk]
        simp [bz, parityUpTo_zero]
    have hfalse := noE_false (y := a) (s := svOf b (elim a 24 yrows)) (col := fun i => colOf i (elim a 24 yrows))
      24 ((T - wt (vec24 a) - 1) / 2) 0 e (fun i hi => ⟨i.2, testBit_false_of_vec24 (he i hi)⟩) (by omega) hbits
    rw [hfalse] at hnoE
    exact absurd hnoE (by decide)

/-- **Soundness of `go`:** if the check passes, every word `a + Σ_{i<n} c_i y_{r+i}` with
`b + Σ_{i<n} c_i z_{r+i}` has the leaf property. -/
theorem go_sound (T : ℕ) : ∀ (n r a b : ℕ), go T n r a b = true →
    ∀ c : Fin n → ZMod 2, LeafProp T (vec24 a + ∑ i : Fin n, c i • vec24 (yrow (r + i)))
      (vec24 b + ∑ i : Fin n, c i • vec24 (zrow (r + i))) := by
  intro n
  induction n with
  | zero =>
    intro r a b h c
    rw [Fin.sum_univ_zero, Fin.sum_univ_zero, add_zero, add_zero]
    exact leaf_sound h
  | succ n ih =>
    intro r a b h c
    simp only [go, Bool.and_eq_true] at h
    have e2 : ∀ (f : ℕ → ℕ) (i : Fin n), vec24 (f (r + 1 + i)) = vec24 (f (r + (i.succ : ℕ))) := by
      intro f i
      rw [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero]
    rcases zmod2_eq_zero_or_one (c 0) with h0 | h0
    · have key := ih (r + 1) a b h.1 (fun i => c i.succ)
      simp only [e2 yrow, e2 zrow] at key
      rw [h0, zero_smul, zero_smul, zero_add, zero_add]
      exact key
    · have key := ih (r + 1) _ _ h.2 (fun i => c i.succ)
      simp only [e2 yrow, e2 zrow, vec24_xor] at key
      rw [h0, one_smul, one_smul, ← add_assoc, ← add_assoc]
      exact key

/-- Every word `y` of `Y48` has the leaf property for `T = 12`, with `z = z_y`. -/
theorem Y48_leaf {y : Fin 24 → ZMod 2} (hy : y ∈ Y48) : LeafProp 12 y (Zlin y) := by
  rw [Y48, Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, rfl⟩ := hy
  have h := go_sound 12 12 0 0 0 go_all c
  simp only [vec24_zero, zero_add] at h
  rw [map_sum]
  simp only [map_smul, Zlin_rowY]
  exact h

/-- `Y48` has minimum weight 6. -/
theorem Y48_minWt : ∀ y ∈ Y48, y ≠ 0 → 6 ≤ wt y := by
  intro y hy hne
  rcases Y48_leaf hy with h0 | ⟨h6, _⟩
  · exact absurd h0 hne
  · exact h6

/-- No nonzero word `y` of `Y48` of weight below 12 has a bad pattern: for every set `e` of coordinates outside
`supp y` with `2|e| < 12 − |y|` some `x ∈ Y48` disjoint from `y` has `⟨𝟙_e, x⟩ ≠ B48(y, x)`. -/
theorem no_bad_pattern (y : Y48) (hy0 : (y : Fin 24 → ZMod 2) ≠ 0) (hw : wt (y : Fin 24 → ZMod 2) < 12)
    (e : Finset (Fin 24)) (he : ∀ i ∈ e, (y : Fin 24 → ZMod 2) i = 0)
    (hcard : 2 * e.card < 12 - wt (y : Fin 24 → ZMod 2)) :
    ∃ x : Y48, (∀ i, (y : Fin 24 → ZMod 2) i = 0 ∨ (x : Fin 24 → ZMod 2) i = 0) ∧
      indicator e ⬝ᵥ (x : Fin 24 → ZMod 2) ≠ B48 y x := by
  rcases Y48_leaf y.2 with h0 | ⟨_, h⟩
  · exact absurd h0 hy0
  · obtain ⟨x, hx, hdisj, hne⟩ := h hw e he hcard
    exact ⟨⟨x, hx⟩, hdisj, hne⟩

/-- **For `H_D`:** the length-48 analog of `H_D` is false; the form `B48 ∈ A_0(Y48)` has no constraint word
with a bad pattern. -/
theorem not_H_D48 : ¬ H_D48 := by
  intro h
  obtain ⟨y, hw, e, he, hcard, hx⟩ := h B48 B48_inA0
  have hy0 : (y : Fin 24 → ZMod 2) ≠ 0 := by
    intro h0
    rw [h0, Three.wt_zero] at hw
    omega
  obtain ⟨x, hdisj, hne⟩ := no_bad_pattern y hy0 (by omega) e he hcard
  exact hne (hx x hdisj)

/-- The code `C_B` of `B48` (T4's Definition 3.1, length 48) has minimum weight 12. -/
theorem CB_B48_minWt : ∀ c ∈ CB Y48 B48, c ≠ 0 → 12 ≤ wt c := by
  intro c hc hne
  obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
  rw [wt_pv_add]
  by_cases hy0 : (y : Fin 24 → ZMod 2) = 0
  · have hzY : z ∈ Y48 := by
      rw [Y48_selfDual]
      intro y' hy'
      rw [hz ⟨y', hy'⟩, B48_apply, hy0, map_zero, zero_dotProduct]
    have hz0 : z ≠ 0 := by
      intro h0
      apply hne
      rw [h0, hy0, add_zero, pv_zero]
    have h6 := Y48_minWt z hzY hz0
    have hcard : #(univ.filter (fun i => (y : Fin 24 → ZMod 2) i = 0 ∧ z i ≠ 0)) = wt z := by
      rw [hy0]
      simp only [Pi.zero_apply, true_and]
      rfl
    rw [hcard, hy0, Three.wt_zero]
    omega
  · by_contra hlt
    have hlt' := Nat.lt_of_not_le hlt
    obtain ⟨x, hdisj, hne'⟩ := no_bad_pattern y hy0 (by omega)
      (univ.filter (fun i => (y : Fin 24 → ZMod 2) i = 0 ∧ z i ≠ 0))
      (fun i hi => (Finset.mem_filter.1 hi).2.1) (by omega)
    apply hne'
    rw [← hz x]
    simp only [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases hdisj i with hyi | hxi
    · have hind : indicator (univ.filter (fun i => (y : Fin 24 → ZMod 2) i = 0 ∧ z i ≠ 0)) i = z i := by
        simp only [indicator, Finset.mem_filter, Finset.mem_univ, true_and, hyi]
        rcases zmod2_eq_zero_or_one (z i) with h | h <;> simp [h]
      rw [hind]
    · rw [hxi, mul_zero, mul_zero]

end C72.T5.HD48
