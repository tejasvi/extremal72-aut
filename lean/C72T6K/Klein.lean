import C72T6.Solutions

/-!
# T6: the second involution (Lemma 3.4), the space `G` and the forms of an instance (Section 3)

On the pairs `ι × 𝔽₂`, with `a = aStd`:
* **Lemma 3.4 (a)** (`pair_form`, `pair_form_props`, `pair_form_fpf`, `mem_Aut_Yof_of_pair_form`): a permutation `b` that
  commutes with `a` is `b (i, e) = (β i, e + t i)`; if `b` is an involution, so is `β`, and `t (β i) = t i`; if `b` and
  `a b` are fixed-point-free, so is `β`; if `b ∈ Aut C`, then `β ∈ Aut Y` for the contracted fixed code `Y` of `C`.
* **Lemma 3.4 (b)** (`exists_swapP`, `swapP_conj`, `permute_swapP_pv_self`, `swapP_mul_aStd`): swapping the two coordinates
  of one pair in each `β`-orbit with `t = 1` conjugates `b` to the lift `(i, e) ↦ (β i, e)`; the swap commutes with `a`
  and fixes every word `(x | x)`.
* **Lemma 3.4 (c)** (`liftP_mem_Aut_CB_iff`): the lift of `g ∈ Aut Y` is an automorphism of `C_B` if and only if `B` is
  `g`-invariant, `B(y g, y' g) = B(y, y')`.
* `A(Y, β)` (`InA`): the symmetric, `β`-invariant forms with (diag); `G` (`GK`): the span of the `D_T` for the sets `T` of
  Lemma 3.5 (b); every `D ∈ G` is `β`-invariant (`formAct_of_mem_GK`), so `A(Y, β)` is a union of cosets of `G`
  (`InA_add`), and `G ≤ G_0`.
* One constraint word from each orbit `{y, y β}` suffices (`badAt_iff_of_invariant`, `ruledOut_iff_reps`), and the forms
  of an instance move with a conjugation of `β` in `Aut Y` (`InA_conj`, `isFPFInv_conj`).
-/

namespace C72.T6

open C72 C72.T4 Module Finset Equiv

variable {ι : Type*}

/-! ## Lifts and swaps of pairs -/

/-- The lift `(i, e) ↦ (β i, e)` of a permutation of the coordinates to the pairs. -/
def liftP (β : Perm ι) : Perm (ι × ZMod 2) :=
  Equiv.prodCongr β (Equiv.refl (ZMod 2))

theorem liftP_apply (β : Perm ι) (i : ι) (e : ZMod 2) : liftP β (i, e) = (β i, e) :=
  rfl

theorem permute_liftP_pv (β : Perm ι) (u v : ι → ZMod 2) :
    permute (liftP β) (pv u v) = pv (permute β u) (permute β v) := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem liftP_mul_aStd (β : Perm ι) : liftP β * aStd = aStd * liftP β := by
  ext ⟨i, e⟩ <;> rfl

theorem liftP_mul (β γ : Perm ι) : liftP (β * γ) = liftP β * liftP γ := by
  ext ⟨i, e⟩ <;> rfl

theorem aStd_apply' (p : ι × ZMod 2) : aStd p = (p.1, p.2 + 1) :=
  rfl

theorem pv_self_apply (x : ι → ZMod 2) (p : ι × ZMod 2) : pv x x p = x p.1 := by
  unfold pv
  split_ifs <;> rfl

/-- `1` on the pairs of `J`, `0` elsewhere. -/
def ind [DecidableEq ι] (J : Finset ι) (i : ι) : ZMod 2 :=
  if i ∈ J then 1 else 0

/-- The swap of the two coordinates of each pair `i ∈ J`: `(i, e) ↦ (i, e + [i ∈ J])`. -/
def swapP [DecidableEq ι] (J : Finset ι) : Perm (ι × ZMod 2) where
  toFun p := (p.1, p.2 + ind J p.1)
  invFun p := (p.1, p.2 + ind J p.1)
  left_inv p := by
    show (p.1, p.2 + ind J p.1 + ind J p.1) = p
    rw [add_assoc, zmod2_add_self', add_zero]
  right_inv p := by
    show (p.1, p.2 + ind J p.1 + ind J p.1) = p
    rw [add_assoc, zmod2_add_self', add_zero]

theorem swapP_apply [DecidableEq ι] (J : Finset ι) (i : ι) (e : ZMod 2) : swapP J (i, e) = (i, e + ind J i) :=
  rfl

theorem swapP_mul_self [DecidableEq ι] (J : Finset ι) : swapP J * swapP J = 1 := by
  ext ⟨i, e⟩
  · rfl
  · show e + ind J i + ind J i = e
    rw [add_assoc, zmod2_add_self', add_zero]

theorem swapP_mul_aStd [DecidableEq ι] (J : Finset ι) : swapP J * aStd = aStd * swapP J := by
  ext ⟨i, e⟩
  · rfl
  · show e + 1 + ind J i = e + ind J i + 1
    rw [add_right_comm]

/-- The swaps fix every word `(x | x)`. -/
theorem permute_swapP_pv_self [DecidableEq ι] (J : Finset ι) (x : ι → ZMod 2) :
    permute (swapP J) (pv x x) = pv x x := by
  funext p
  rw [permute_apply, pv_self_apply, pv_self_apply]
  rfl

/-! ## Lemma 3.4 (a): a permutation commuting with `a` -/

/-- **Lemma 3.4 (a)**, the form of `b`: a permutation of the pairs that commutes with `a` maps pairs to pairs,
`b (i, e) = (β i, e + t i)`. -/
theorem pair_form [Finite ι] (b : Perm (ι × ZMod 2)) (hb : b * aStd = aStd * b) :
    ∃ β : Perm ι, ∃ t : ι → ZMod 2, ∀ i e, b (i, e) = (β i, e + t i) := by
  have hb' : ∀ p, b (aStd p) = aStd (b p) := fun p => congrArg (fun f : Perm (ι × ZMod 2) => f p) hb
  have hform : ∀ i e, b (i, e) = ((b (i, 0)).1, e + (b (i, 0)).2) := by
    intro i e
    rcases zmod2_cases e with rfl | rfl
    · exact Prod.ext rfl (zero_add _).symm
    · have h1 : ((i, 1) : ι × ZMod 2) = aStd (i, 0) := by rw [aStd_apply, zero_add]
      rw [h1, hb', aStd_apply', add_comm]
  have hinj : Function.Injective (fun i => (b (i, 0)).1) := by
    intro i j hij
    simp only at hij
    by_cases h2 : (b (i, 0)).2 = (b (j, 0)).2
    · exact congrArg Prod.fst (b.injective (Prod.ext hij h2))
    · have key : ∀ x y : ZMod 2, x ≠ y → y = x + 1 := by decide
      have h3 := key _ _ h2
      have h4 : b (j, 0) = b (i, 1) := by
        rw [hform i 1]
        exact Prod.ext hij.symm (by rw [h3, add_comm])
      have h5 := congrArg Prod.snd (b.injective h4)
      exact absurd h5 (by decide : (0 : ZMod 2) ≠ 1)
  exact ⟨Equiv.ofBijective _ hinj.bijective_of_finite, fun i => (b (i, 0)).2, fun i e => hform i e⟩

/-- **Lemma 3.4 (a)**: if `b` is an involution, then `β² = 1` and `t (β i) = t i`. -/
theorem pair_form_props {b : Perm (ι × ZMod 2)} {β : Perm ι} {t : ι → ZMod 2}
    (hbt : ∀ i e, b (i, e) = (β i, e + t i)) (hb2 : b * b = 1) : β * β = 1 ∧ ∀ i, t (β i) = t i := by
  have key : ∀ i, β (β i) = i ∧ t (β i) = t i := by
    intro i
    have h : b (b (i, 0)) = (i, 0) := congrArg (fun f : Perm (ι × ZMod 2) => f (i, 0)) hb2
    rw [hbt i 0, hbt] at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [zero_add] at h2
    exact ⟨h1, zmod2_eq_of_add_eq_zero _ _ h2⟩
  exact ⟨Equiv.ext fun i => (key i).1, fun i => (key i).2⟩

/-- **Lemma 3.4 (a)**: if `b` and `a b` are fixed-point-free, so is `β`. -/
theorem pair_form_fpf {b : Perm (ι × ZMod 2)} {β : Perm ι} {t : ι → ZMod 2}
    (hbt : ∀ i e, b (i, e) = (β i, e + t i)) (hb : ∀ p, b p ≠ p)
    (hab : ∀ p, ((aStd : Perm (ι × ZMod 2)) * b) p ≠ p) :
    ∀ i, β i ≠ i := by
  intro i hi
  rcases zmod2_cases (t i) with h | h
  · apply hb (i, 0)
    rw [hbt, hi, h, add_zero]
  · apply hab (i, 0)
    rw [Perm.mul_apply, hbt, hi, h, aStd_apply, zero_add, zmod2_add_self']

theorem permute_pv_self_of_pair_form {b : Perm (ι × ZMod 2)} {β : Perm ι} {t : ι → ZMod 2}
    (hbt : ∀ i e, b (i, e) = (β i, e + t i)) (x : ι → ZMod 2) :
    permute b (pv x x) = pv (permute β x) (permute β x) := by
  funext p
  rw [permute_apply, pv_self_apply, pv_self_apply, permute_apply]
  congr 1
  have h := hbt (b.symm p).1 (b.symm p).2
  rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
  have h1 : p.1 = β (b.symm p).1 := congrArg Prod.fst h
  exact ((Equiv.symm_apply_eq β).2 h1).symm

/-- **Lemma 3.4 (a)**: `β ∈ Aut Y` for the contracted fixed code `Y` of `C`, when `b ∈ Aut C`. -/
theorem mem_Aut_Yof_of_pair_form [Fintype ι] {C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)} {b : Perm (ι × ZMod 2)}
    (hbC : b ∈ Aut C) {β : Perm ι} {t : ι → ZMod 2} (hbt : ∀ i e, b (i, e) = (β i, e + t i)) :
    β ∈ Aut (Yof C) := by
  rw [mem_Aut_iff]
  intro x hx
  rw [mem_Yof] at hx ⊢
  rw [← permute_pv_self_of_pair_form hbt]
  exact permute_mem_of_mem_Aut hbC hx

/-! ## Lemma 3.4 (b): the swap that removes `t` -/

/-- **Lemma 3.4 (b)**, the choice of the pairs to swap: one element of each `β`-orbit with `t = 1`. -/
theorem exists_swapP [DecidableEq ι] [LinearOrder ι] [Fintype ι] {β : Perm ι} {t : ι → ZMod 2}
    (hβ2 : β * β = 1) (hfp : ∀ i, β i ≠ i) (ht : ∀ i, t (β i) = t i) :
    ∃ J : Finset ι, ∀ i, ind J i + ind J (β i) = t i := by
  have hββ : ∀ i, β (β i) = i := fun i => congrArg (fun f : Perm ι => f i) hβ2
  refine ⟨univ.filter (fun i => t i = 1 ∧ i < β i), fun i => ?_⟩
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and, hββ, ht]
  rcases zmod2_cases (t i) with h | h
  · simp [h]
  · rcases lt_or_gt_of_ne (hfp i).symm with hlt | hlt
    · simp [h, hlt, not_lt.2 hlt.le]
    · simp [h, hlt, not_lt.2 hlt.le]

/-- **Lemma 3.4 (b)**: the swap conjugates `b` to the lift of `β`. -/
theorem swapP_conj [DecidableEq ι] {b : Perm (ι × ZMod 2)} {β : Perm ι} {t : ι → ZMod 2}
    (hbt : ∀ i e, b (i, e) = (β i, e + t i)) {J : Finset ι} (hJ : ∀ i, ind J i + ind J (β i) = t i) :
    swapP J * b * swapP J = liftP β := by
  ext ⟨i, e⟩
  · show (b (swapP J (i, e))).1 = β i
    rw [swapP_apply, hbt]
  · show (b (swapP J (i, e))).2 + ind J (b (swapP J (i, e))).1 = e
    rw [swapP_apply, hbt]
    have key : ∀ e a c s : ZMod 2, a + c = s → e + a + s + c = e := by decide
    exact key _ _ _ _ (hJ i)

/-! ## Lemma 3.4 (c) -/

variable [Fintype ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- **Lemma 3.4 (c).** For `g ∈ Aut Y` the lift `(i, e) ↦ (g i, e)` is an automorphism of `C_B` if and only if `B` is
`g`-invariant. -/
theorem liftP_mem_Aut_CB_iff (g : Aut Y) (B : LinearMap.BilinForm (ZMod 2) Y) :
    liftP (g : Perm ι) ∈ Aut (CB Y B) ↔ formAct g B = B := by
  rw [mem_Aut_iff]
  constructor
  · intro h
    ext y y'
    obtain ⟨z, hz⟩ := exists_dotProduct_eq (B y)
    have hc := h _ (mem_CB.2 ⟨y, z, hz, rfl⟩)
    rw [permute_liftP_pv, map_add] at hc
    obtain ⟨y'', z'', hz'', heq⟩ := mem_CB.1 hc
    obtain ⟨h1, h2⟩ := pv_inj heq
    have hy'' : y'' = autLin g y := by
      apply Subtype.ext
      rw [autLin_coe]
      have h3 : z'' + (y'' : ι → ZMod 2) = z'' + permute (g : Perm ι) (y : ι → ZMod 2) := by rw [← h2, h1]
      exact add_left_cancel h3
    have h4 := hz'' (autLin g y')
    rw [← h1, hy'', autLin_coe, dotProduct_permute, hz] at h4
    rw [formAct_apply]
    exact h4.symm
  · intro hB c hc
    obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
    rw [permute_liftP_pv, map_add]
    refine mem_CB.2 ⟨autLin g y, permute (g : Perm ι) z, fun w => ?_, by rw [autLin_coe]⟩
    have hw : w = autLin g (autLin g⁻¹ w) := (autLin_inv_apply g w).symm
    rw [hw, autLin_coe, dotProduct_permute, hz, ← formAct_apply, hB]

/-! ## The forms of an instance: `A(Y, β)` and the space `G` -/

/-- A fixed-point-free involution. -/
def IsFPFInv {κ : Type*} (β : Perm κ) : Prop :=
  β * β = 1 ∧ ∀ i, β i ≠ i

/-- `A(Y, β)`: the symmetric, `β`-invariant forms that satisfy (diag). -/
def InA (Y : Submodule (ZMod 2) (ι → ZMod 2)) (h1 : allOnes ∈ Y) (β : Aut Y) (B : LinearMap.BilinForm (ZMod 2) Y) :
    Prop :=
  InA0 Y h1 B ∧ formAct β B = B

/-- The paper's `G` (Lemma 3.5 (c)): the span of the forms `D_T` for the sets `T` that are unions of `β`-orbits or contain
exactly one element of each `β`-orbit. -/
def GK (β : Aut Y) : Submodule (ZMod 2) (LinearMap.BilinForm (ZMod 2) Y) :=
  Submodule.span (ZMod 2)
    {D | ∃ T : Finset ι, ((∀ i, (β : Perm ι) i ∈ T ↔ i ∈ T) ∨ (∀ i, (β : Perm ι) i ∈ T ↔ i ∉ T)) ∧ D = DT Y T}

omit [Fintype ι] in
theorem GK_le_G0 (β : Aut Y) : GK β ≤ G0 Y :=
  Submodule.span_le.2 (by
    rintro _ ⟨T, -, rfl⟩
    exact Submodule.subset_span ⟨T, rfl⟩)

/-- `G` has an echelon basis. -/
theorem exists_echelonBasis_GK (β : Aut Y) :
    ∃ m, Nonempty (EchelonBasis (V := LinearMap.BilinForm (ZMod 2) Y) (GK β) m) :=
  exists_echelonBasis_of_finite (V := LinearMap.BilinForm (ZMod 2) Y)
    ((Set.finite_range (DT Y)).subset (by
      rintro _ ⟨T, -, rfl⟩
      exact ⟨T, rfl⟩)) rfl

omit [Fintype ι] in
/-- **Lemma 3.5 (b)**, for forms: `D_T` is `β`-invariant when `T` is a union of `β`-orbits. -/
theorem formAct_DT_of_invariant (β : Aut Y) {T : Finset ι} (hT : ∀ i, (β : Perm ι) i ∈ T ↔ i ∈ T) :
    formAct β (DT Y T) = DT Y T := by
  rw [formAct_DT]
  congr 1
  ext i
  rw [Finset.mem_map_equiv, Equiv.symm_symm, hT]

/-- **Lemma 3.5 (b)**, for forms: `D_T` is `β`-invariant when `T` contains exactly one element of each `β`-orbit
(`Y` self-dual). -/
theorem formAct_DT_of_transversal [DecidableEq ι] (hY : SelfDual Y) (β : Aut Y) {T : Finset ι}
    (hT : ∀ i, (β : Perm ι) i ∈ T ↔ i ∉ T) : formAct β (DT Y T) = DT Y T := by
  have hmap : T.map (β : Perm ι).symm.toEmbedding = Tᶜ := by
    ext i
    rw [Finset.mem_map_equiv, Equiv.symm_symm, hT, Finset.mem_compl]
  rw [formAct_DT, hmap]
  ext y y'
  rw [DT_apply, DT_apply]
  have h := Finset.sum_compl_add_sum T (fun i => (y : ι → ZMod 2) i * (y' : ι → ZMod 2) i)
  have h0 : ∑ i, (y : ι → ZMod 2) i * (y' : ι → ZMod 2) i = 0 := dotProduct_eq_zero_of_selfDual hY y.2 y'.2
  rw [h0] at h
  exact (zmod2_eq_of_add_eq_zero _ _ h).symm

/-- Every `D ∈ G` is `β`-invariant. -/
theorem formAct_of_mem_GK [DecidableEq ι] (hY : SelfDual Y) (β : Aut Y) : ∀ D ∈ GK β, formAct β D = D := by
  intro D hD
  induction hD using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT | hT, rfl⟩ := hx
    · exact formAct_DT_of_invariant β hT
    · exact formAct_DT_of_transversal hY β hT
  | zero =>
    ext x x'
    rfl
  | add x y _ _ hx hy => rw [formAct_add, hx, hy]
  | smul a x _ hx =>
    have hs : formAct β (a • x) = a • formAct β x := by
      ext u u'
      rfl
    rw [hs, hx]

/-- `A(Y, β)` is a union of cosets of `G`. -/
theorem InA_add [DecidableEq ι] (hY : SelfDual Y) {h1 : allOnes ∈ Y} {β : Aut Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hB : InA Y h1 β B) {D : LinearMap.BilinForm (ZMod 2) Y} (hD : D ∈ GK β) : InA Y h1 β (B + D) :=
  ⟨InA0_add hB.1 (GK_le_G0 β hD), by rw [formAct_add, hB.2, formAct_of_mem_GK hY β D hD]⟩

/-! ## One constraint word from each orbit; conjugation of `β` -/

/-- If `B^g` has a bad syndrome at `y`, then `B` has one at `y g`. -/
theorem badAt_formAct [DecidableEq ι] (g : Aut Y) {B : LinearMap.BilinForm (ZMod 2) Y} {y : Y}
    (h : BadAt Y (formAct g B) y) : BadAt Y B (autLin g y) := by
  obtain ⟨e, he, hcard, hsyn⟩ := h
  refine ⟨e.map (g : Equiv.Perm ι).toEmbedding, ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_map_equiv] at hi
    rw [autLin_coe, permute_apply]
    exact he _ hi
  · rw [Finset.card_map, autLin_coe, wt_permute]
    exact hcard
  · intro x hx
    have hx0 : ∀ i, (y : ι → ZMod 2) i = 0 ∨ (autLin g⁻¹ x : ι → ZMod 2) i = 0 := by
      intro i
      have := hx ((g : Equiv.Perm ι) i)
      rw [autLin_coe, permute_apply_self] at this
      rw [autLin_coe]
      exact this
    have h2 := hsyn (autLin g⁻¹ x) hx0
    rw [formAct_apply, autLin_inv_apply] at h2
    rw [← h2, indicator_map]
    conv_lhs => rw [← autLin_inv_apply g x, autLin_coe]
    rw [dotProduct_permute]

/-- For a `β`-invariant form the syndrome condition at `y β` is the one at `y` (Section 3.4). -/
theorem badAt_iff_of_invariant [DecidableEq ι] (β : Aut Y) (hβ2 : (β : Perm ι) * β = 1)
    {B : LinearMap.BilinForm (ZMod 2) Y} (hB : formAct β B = B) (y : Y) :
    BadAt Y B (autLin β y) ↔ BadAt Y B y := by
  have hyy : autLin β (autLin β y) = y := by
    rw [← autLin_mul]
    have hββ : β * β = 1 := Subtype.ext hβ2
    rw [hββ]
    rfl
  constructor
  · intro h
    have h' : BadAt Y (formAct β B) (autLin β y) := by
      rw [hB]
      exact h
    have h'' := badAt_formAct β h'
    rwa [hyy] at h''
  · intro h
    have h' : BadAt Y (formAct β B) y := by
      rw [hB]
      exact h
    exact badAt_formAct β h'

/-- **One word from each orbit `{y, y β}` suffices.** For a `β`-invariant form, `RuledOut` holds if and only if a bad
syndrome occurs at a constraint word of `R`, for every set `R` that contains `y` or `y β` for each constraint word `y`. -/
theorem ruledOut_iff_reps [DecidableEq ι] (β : Aut Y) (hβ2 : (β : Perm ι) * β = 1)
    {B : LinearMap.BilinForm (ZMod 2) Y} (hB : formAct β B = B) (R : Set Y)
    (hR : ∀ y : Y, IsConstraint (y : ι → ZMod 2) → y ∈ R ∨ autLin β y ∈ R) :
    RuledOut Y B ↔ ∃ y ∈ R, IsConstraint (y : ι → ZMod 2) ∧ BadAt Y B y := by
  constructor
  · rintro ⟨y, hy, hbad⟩
    rcases hR y hy with h | h
    · exact ⟨y, h, hy, hbad⟩
    · refine ⟨autLin β y, h, ?_, (badAt_iff_of_invariant β hβ2 hB y).2 hbad⟩
      unfold IsConstraint at hy ⊢
      rw [autLin_coe, wt_permute]
      exact hy
  · rintro ⟨y, -, hy, hbad⟩
    exact ⟨y, hy, hbad⟩

/-- A conjugate of a fixed-point-free involution is one. -/
theorem isFPFInv_conj {κ : Type*} {β : Perm κ} (hβ : IsFPFInv β) (g : Perm κ) : IsFPFInv (g⁻¹ * β * g) := by
  refine ⟨?_, fun i hi => hβ.2 (g i) ?_⟩
  · calc g⁻¹ * β * g * (g⁻¹ * β * g) = g⁻¹ * (β * β) * g := by group
      _ = 1 := by rw [hβ.1]; group
  · have h := congrArg g hi
    simpa [Perm.mul_apply] using h

/-- **The forms of an instance move with a conjugation of `β`** in `Aut Y` (Proposition 3.7: `β` may be taken from a
set of representatives): `B ↦ B^g` maps `A(Y, β)` into `A(Y, g⁻¹ β g)`, and `B^g` is ruled out only if `B` is. -/
theorem InA_conj [DecidableEq ι] {h1 : allOnes ∈ Y} {β : Aut Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hB : InA Y h1 β B) (g : Aut Y) :
    InA Y h1 (g⁻¹ * β * g) (formAct g B) ∧ (RuledOut Y (formAct g B) → RuledOut Y B) := by
  refine ⟨⟨InA0_formAct hB.1 g, ?_⟩, ruledOut_of_ruledOut_formAct g⟩
  rw [← formAct_mul, show g * (g⁻¹ * β * g) = β * g by group, formAct_mul, hB.2]

end C72.T6
