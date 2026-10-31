import C72T5.Main

/-!
# The Main Theorem with a weaker form of (L2)

T4's `H_L2` assumes that the contracted fixed code of a fixed-point-free involution `a` of an extremal code is self-dual
with minimum weight exactly 8. Its half "minimum weight at least 8" follows from `Ext72` (`minWt_contracted_of_Ext72`): a
nonzero word `u` of the contracted code gives the nonzero word `expand a u` of `C`, of weight `2 |u|`
(`wt_expand_involution`). `H_L2_sd` keeps only the rest of (L2): self-duality and a word of weight 8 (the bound `d ≤ 8`
for self-dual codes of length 36, which is not proved here).

`H_L2 → H_L2_sd` is immediate (`H_L2_sd_of_H_L2`) and `H_L2_sd → H_L2` is `H_L2_of_sd`, so `noFPFInv_of'`,
`mainTheorem_weaker` and `mainTheorem_weaker_paper` are T4's `noFPFInv_of` and T5's `mainTheorem`, `mainTheorem_paper`
with `H_L2_sd` in place of `H_L2`: they assume less of [Nebe12, Thm 3.1]. The original `H_L2` and `mainTheorem` are
unchanged.
-/

namespace C72

open C72.T4 Finset Equiv

/-- `|expand a u| = 2 |u|` for a fixed-point-free involution `a`: each orbit has two coordinates. -/
theorem wt_expand_involution {ι : Type*} [Fintype ι] [DecidableEq ι] {a : Perm ι} (ha2 : a * a = 1)
    (hfp : ∀ i, a i ≠ i) (u : Orbits a → ZMod 2) : wt (expand a u) = 2 * wt u := by
  rw [wt_eq_sum, wt_eq_sum, Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ (toOrbit a)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  have hfib : ∀ j ∈ univ.filter (fun j => toOrbit a j = ω),
      (if expand a u j ≠ 0 then (1 : ℕ) else 0) = if u ω ≠ 0 then 1 else 0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [expand_apply, hj.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, card_fiber_involution ha2 hfp ω, smul_eq_mul]

/-- If `C` has minimum weight at least `2 d`, the contracted fixed code of a fixed-point-free involution has minimum weight
at least `d`. -/
theorem minWt_contracted {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Submodule (ZMod 2) (ι → ZMod 2)} {d : ℕ}
    (hC : MinWt C (2 * d)) {a : Perm ι} (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) : MinWt (contracted a C) d := by
  intro u hu hu0
  have hne : expand a u ≠ 0 := by
    intro h
    apply hu0
    funext ω
    obtain ⟨j, rfl⟩ := toOrbit_surjective a ω
    have hj := congrFun h j
    rwa [expand_apply] at hj
  have h := hC (expand a u) ((mem_contracted a).1 hu) hne
  rw [wt_expand_involution ha2 hfp] at h
  omega

/-- **The minimum-weight half of (L2) from `Ext72`.** -/
theorem minWt_contracted_of_Ext72 {C : Code 72} (hC : Ext72 C) {a : Perm (Fin 72)} (hord : orderOf a = 2)
    (hfp : ∀ i, a i ≠ i) : MinWt (contracted a C) 8 :=
  minWt_contracted (d := 8) hC.2.1 (mul_self_eq_one_of_orderOf_two hord) hfp

/-- **`H_L2_sd`**: (L2) without the part that follows from `Ext72`. The contracted fixed code of a fixed-point-free
involution of an extremal code is self-dual and has a word of weight 8. -/
def H_L2_sd : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → (∀ i, a i ≠ i) →
    SelfDual (contracted a C) ∧ ∃ x ∈ contracted a C, wt x = 8

theorem H_L2_sd_def : H_L2_sd ↔ ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → (∀ i, a i ≠ i) →
    SelfDual (contracted a C) ∧ ∃ x ∈ contracted a C, wt x = 8 :=
  Iff.rfl

/-- `H_L2` gives `H_L2_sd`. -/
theorem H_L2_sd_of_H_L2 (h : T4.H_L2) : H_L2_sd := by
  intro C hC a ha hord hfp
  obtain ⟨hsd, -, x, hx, hwx⟩ := h C hC a ha hord hfp
  exact ⟨hsd, x, hx, hwx⟩

/-- `H_L2_sd` gives `H_L2`, with `minWt_contracted_of_Ext72`. -/
theorem H_L2_of_sd (h : H_L2_sd) : T4.H_L2 := by
  intro C hC a ha hord hfp
  obtain ⟨hsd, x, hx, hwx⟩ := h C hC a ha hord hfp
  exact ⟨hsd, minWt_contracted_of_Ext72 hC hord hfp, x, hx, hwx⟩

/-- No fixed-point-free involution, from `H_L2_sd`, `H_L3` and the 41 searches. -/
theorem noFPFInv_of' (hL2 : H_L2_sd) (hL3 : T4.H_L3) (hD : ∀ k, T4.H_D k) : NoFPFInv :=
  T4.noFPFInv_of (H_L2_of_sd hL2) hL3 hD

/-- **The Main Theorem with `H_L2_sd` in place of `H_L2`.** -/
theorem mainTheorem_weaker (h1 : H_primes) (h2 : H_L1) (h3 : H_L2_sd) (h4 : T4.H_L3) (h5 : H_CP5) (h6 : H_CP3)
    (h7 : H_16) (h8 : H_Golay) (h9 : H_LP) (hA : H_A) (hCB : H_CB) (hD : ∀ k, T4.H_D k) :
    ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  mainTheorem h1 h2 (H_L2_of_sd h3) h4 h5 h6 h7 h8 h9 hA hCB hD

/-- The same in the paper's terms (T1's `PaperMain`). -/
theorem mainTheorem_weaker_paper (h1 : H_primes) (h2 : H_L1) (h3 : H_L2_sd) (h4 : T4.H_L3) (h5 : H_CP5)
    (h6 : H_CP3) (h7 : H_16) (h8 : H_Golay) (h9 : H_LP) (hA : H_A) (hCB : H_CB) (hD : ∀ k, T4.H_D k) : PaperMain :=
  mainTheorem_paper h1 h2 (H_L2_of_sd h3) h4 h5 h6 h7 h8 h9 hA hCB hD

end C72
