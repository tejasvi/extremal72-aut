import C72T3.MDef

/-!
# T6 (order 5): the collineations of the Fano plane, and the invariance of `M` under them

The cycles of one side are the points `0, …, 6` of the Fano plane with the lines `T3.fanoLines` (Sec. 2.2). A
collineation is a permutation of the points that maps every line to a line (`IsColl`). They form a group
(`isColl_one`, `isColl_mul`, `isColl_inv`).

* A collineation `σ` is determined by `σ 0`, `σ 1`, `σ 2`, a triple of non-collinear points: the images of `3, 4, 5, 6`
  are third points of the lines `{0,1,3}`, `{1,2,4}`, `{2,3,5}`, `{6,0,2}` (`coe_eq_tableOf`). Conversely, for every
  ordered triple `(a, b, c)` of non-collinear points the table `tableOf a b c` is a collineation (`collOf`; checked by
  the Bool function `triplesOK` with the soundness lemmas `linesOK_sound`, `injOK_sound`). So `σ ↦ (σ 0, σ 1, σ 2)` is
  a bijection onto `ncTriples` (`collEquiv`), and there are 168 collineations (`card_collineations`).
* The collineations are transitive on the points (`exists_isColl_apply_eq_zero`).
* A collineation maps the 16 words `(S, x)` of `e8` to words (`image_mem_e8Words`), so `M(v ∘ σ) = M(v)` (`M_comp`).
-/

namespace C72.T6O5

open C72.T3 Finset Equiv

/-- A collineation of the Fano plane of Sec. 2.2: a permutation of the points that maps each line to a line. -/
def IsColl (σ : Perm (Fin 7)) : Prop :=
  ∀ L ∈ fanoLines, L.image σ ∈ fanoLines

/-- The third point of the line through two distinct points `x` and `y` (`third_mem`, `third_of_mem_line`);
`third x x = x`. -/
def third : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 3, 6, 1, 5, 4, 2], ![3, 1, 4, 0, 2, 6, 5], ![6, 4, 2, 5, 1, 3, 0], ![1, 0, 5, 3, 6, 2, 4],
    ![5, 2, 1, 6, 4, 0, 3], ![4, 6, 3, 2, 0, 5, 1], ![2, 5, 0, 4, 3, 1, 6]]

theorem third_mem : ∀ a b : Fin 7, a ≠ b → ({a, b, third a b} : Finset (Fin 7)) ∈ fanoLines := by
  decide +kernel

/-- Of three distinct points on a line, each is the third point of the line through the other two. -/
theorem third_of_mem_line : ∀ L ∈ fanoLines, ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L, x ≠ y → z ≠ x → z ≠ y →
    z = third x y := by
  decide +kernel

/-- The map with `0 ↦ a`, `1 ↦ b`, `2 ↦ c`, and `3, 4, 5, 6` sent to third points as the lines `{0,1,3}`, `{1,2,4}`,
`{2,3,5}`, `{6,0,2}` require. -/
def tableOf (a b c : Fin 7) : Fin 7 → Fin 7 :=
  ![a, b, c, third a b, third b c, third c (third a b), third c a]

/-- `(a, b, c)` is an ordered triple of non-collinear points. -/
def NC (a b c : Fin 7) : Prop :=
  a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c ≠ third a b

instance (a b c : Fin 7) : Decidable (NC a b c) := by
  unfold NC
  infer_instance

/-- The ordered triples of non-collinear points. -/
def ncTriples : Finset (Fin 7 × Fin 7 × Fin 7) :=
  univ.filter fun p => NC p.1 p.2.1 p.2.2

theorem mem_ncTriples {p : Fin 7 × Fin 7 × Fin 7} : p ∈ ncTriples ↔ NC p.1 p.2.1 p.2.2 := by
  simp only [ncTriples, mem_filter, mem_univ, true_and]

theorem card_ncTriples : #ncTriples = 168 := by decide +kernel

/-! ## The Bool check of the tables -/

/-- The seven lines of `fanoLines` as triples of points. -/
def lineTriples : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]

/-- `f` maps the three points `x, y, z` of each line to distinct `f x`, `f y` and `f z = third (f x) (f y)`. -/
def linesOK (f : Fin 7 → Fin 7) : Bool :=
  lineTriples.all fun l => f l.1 != f l.2.1 && f l.2.2 == third (f l.1) (f l.2.1)

/-- `f` is injective. -/
def injOK (f : Fin 7 → Fin 7) : Bool :=
  (List.finRange 7).all fun x => (List.finRange 7).all fun y => x == y || f x != f y

def tripleOK (a b c : Fin 7) : Bool :=
  !decide (NC a b c) || (linesOK (tableOf a b c) && injOK (tableOf a b c))

/-- The check over all ordered triples. -/
def triplesOK : Bool :=
  (List.finRange 7).all fun a => (List.finRange 7).all fun b => (List.finRange 7).all fun c => tripleOK a b c

theorem triplesOK_eq_true : triplesOK = true := by decide +kernel

theorem tripleOK_eq_true (a b c : Fin 7) : tripleOK a b c = true :=
  List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 triplesOK_eq_true a (List.mem_finRange a)) b
    (List.mem_finRange b)) c (List.mem_finRange c)

theorem linesOK_sound {f : Fin 7 → Fin 7} (h : linesOK f = true) : ∀ L ∈ fanoLines, L.image f ∈ fanoLines := by
  simp only [linesOK, lineTriples, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
    beq_iff_eq] at h
  obtain ⟨⟨h01, h3⟩, ⟨h12, h4⟩, ⟨h23, h5⟩, ⟨h34, h6⟩, ⟨h45, h0⟩, ⟨h56, h1⟩, ⟨h60, h2⟩⟩ := h
  intro L hL
  simp only [fanoLines, mem_insert, mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [image_insert, image_singleton]
  · rw [h3]
    exact third_mem _ _ h01
  · rw [h4]
    exact third_mem _ _ h12
  · rw [h5]
    exact third_mem _ _ h23
  · rw [h6]
    exact third_mem _ _ h34
  · rw [h0]
    exact third_mem _ _ h45
  · rw [h1]
    exact third_mem _ _ h56
  · rw [h2]
    exact third_mem _ _ h60

theorem injOK_sound {f : Fin 7 → Fin 7} (h : injOK f = true) : Function.Injective f := by
  intro x y hxy
  have h' := List.all_eq_true.1 (List.all_eq_true.1 h x (List.mem_finRange x)) y (List.mem_finRange y)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h'
  rcases h' with h' | h'
  · exact h'
  · exact absurd hxy h'

theorem tableOf_ok {a b c : Fin 7} (h : NC a b c) :
    linesOK (tableOf a b c) = true ∧ injOK (tableOf a b c) = true := by
  have h' := tripleOK_eq_true a b c
  simp only [tripleOK, decide_eq_true h, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h'
  exact h'

/-- The collineation with table `tableOf a b c`, for non-collinear `a, b, c`. -/
noncomputable def collOf (a b c : Fin 7) (h : NC a b c) : Perm (Fin 7) :=
  Equiv.ofBijective (tableOf a b c) (Finite.injective_iff_bijective.1 (injOK_sound (tableOf_ok h).2))

theorem coe_collOf {a b c : Fin 7} (h : NC a b c) : ⇑(collOf a b c h) = tableOf a b c :=
  rfl

theorem isColl_collOf {a b c : Fin 7} (h : NC a b c) : IsColl (collOf a b c h) :=
  linesOK_sound (tableOf_ok h).1

/-! ## A collineation is determined by the images of `0, 1, 2` -/

theorem apply_eq_third {σ : Perm (Fin 7)} (hσ : IsColl σ) {L : Finset (Fin 7)} (hL : L ∈ fanoLines)
    {x y z : Fin 7} (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    σ z = third (σ x) (σ y) :=
  third_of_mem_line _ (hσ L hL) _ (mem_image_of_mem σ hx) _ (mem_image_of_mem σ hy) _ (mem_image_of_mem σ hz)
    (σ.injective.ne hxy) (σ.injective.ne hzx) (σ.injective.ne hzy)

theorem apply_three {σ : Perm (Fin 7)} (hσ : IsColl σ) : σ 3 = third (σ 0) (σ 1) :=
  apply_eq_third hσ (L := {0, 1, 3}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem coe_eq_tableOf {σ : Perm (Fin 7)} (hσ : IsColl σ) : ⇑σ = tableOf (σ 0) (σ 1) (σ 2) := by
  have h3 := apply_three hσ
  have h4 : σ 4 = third (σ 1) (σ 2) :=
    apply_eq_third hσ (L := {1, 2, 4}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : σ 5 = third (σ 2) (σ 3) :=
    apply_eq_third hσ (L := {2, 3, 5}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h6 : σ 6 = third (σ 2) (σ 0) :=
    apply_eq_third hσ (L := {6, 0, 2}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  rw [h3] at h5
  funext k
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem nc_of_isColl {σ : Perm (Fin 7)} (hσ : IsColl σ) : NC (σ 0) (σ 1) (σ 2) := by
  refine ⟨σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide), ?_⟩
  rw [← apply_three hσ]
  exact σ.injective.ne (by decide)

theorem isColl_ext {σ τ : Perm (Fin 7)} (hσ : IsColl σ) (hτ : IsColl τ) (h0 : σ 0 = τ 0) (h1 : σ 1 = τ 1)
    (h2 : σ 2 = τ 2) : σ = τ := by
  apply Equiv.ext
  intro k
  rw [coe_eq_tableOf hσ, coe_eq_tableOf hτ, h0, h1, h2]

/-- The collineations correspond to the ordered triples of non-collinear points by `σ ↦ (σ 0, σ 1, σ 2)`. -/
noncomputable def collEquiv : {σ : Perm (Fin 7) // IsColl σ} ≃ {p : Fin 7 × Fin 7 × Fin 7 // p ∈ ncTriples} where
  toFun σ := ⟨(σ.1 0, σ.1 1, σ.1 2), mem_ncTriples.2 (nc_of_isColl σ.2)⟩
  invFun p := ⟨collOf p.1.1 p.1.2.1 p.1.2.2 (mem_ncTriples.1 p.2), isColl_collOf _⟩
  left_inv σ := Subtype.ext (isColl_ext (isColl_collOf (nc_of_isColl σ.2)) σ.2 rfl rfl rfl)
  right_inv _ := rfl

/-- There are 168 collineations. -/
theorem card_collineations : Nat.card {σ : Perm (Fin 7) // IsColl σ} = 168 := by
  rw [Nat.card_congr collEquiv, Nat.card_eq_fintype_card, Fintype.card_coe, card_ncTriples]

/-! ## The collineations form a group, transitive on the points -/

theorem isColl_one : IsColl 1 := fun L hL => by
  rw [Perm.coe_one, image_id]
  exact hL

theorem isColl_mul {σ τ : Perm (Fin 7)} (hσ : IsColl σ) (hτ : IsColl τ) : IsColl (σ * τ) := fun L hL => by
  rw [Perm.coe_mul, ← image_image]
  exact hσ _ (hτ L hL)

theorem isColl_pow {σ : Perm (Fin 7)} (hσ : IsColl σ) : ∀ n : ℕ, IsColl (σ ^ n)
  | 0 => by
    rw [pow_zero]
    exact isColl_one
  | n + 1 => by
    rw [pow_succ]
    exact isColl_mul (isColl_pow hσ n) hσ

theorem isColl_inv {σ : Perm (Fin 7)} (hσ : IsColl σ) : IsColl σ⁻¹ := by
  have h : σ⁻¹ = σ ^ (orderOf σ - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
  rw [h]
  exact isColl_pow hσ _

theorem exists_nc_apply_eq_zero : ∀ i : Fin 7, ∃ a b c : Fin 7, NC a b c ∧ tableOf a b c i = 0 := by
  decide +kernel

/-- The collineations are transitive on the points. -/
theorem exists_isColl_apply_eq_zero (i : Fin 7) : ∃ σ : Perm (Fin 7), IsColl σ ∧ σ i = 0 := by
  obtain ⟨a, b, c, h, hi⟩ := exists_nc_apply_eq_zero i
  exact ⟨collOf a b c h, isColl_collOf h, hi⟩

/-! ## Invariance of `M` -/

theorem image_compl_perm (σ : Perm (Fin 7)) (S : Finset (Fin 7)) : Sᶜ.image σ = (S.image σ)ᶜ := by
  ext k
  simp only [mem_image, mem_compl]
  constructor
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)
  · intro hk
    exact ⟨σ.symm k, fun h => hk ⟨σ.symm k, h, σ.apply_symm_apply k⟩, σ.apply_symm_apply k⟩

/-- A collineation maps the words of `e8` to words. -/
theorem image_mem_e8Words {σ : Perm (Fin 7)} (hσ : IsColl σ) {Sx : Finset (Fin 7) × ℕ} (h : Sx ∈ e8Words) :
    (Sx.1.image σ, Sx.2) ∈ e8Words := by
  rw [e8Words, mem_insert, mem_insert, mem_union, mem_image, mem_image] at h
  rw [e8Words, mem_insert, mem_insert, mem_union, mem_image, mem_image]
  rcases h with rfl | rfl | ⟨L, hL, rfl⟩ | ⟨L, hL, rfl⟩
  · left
    rw [image_empty]
  · right
    left
    rw [image_univ_equiv]
  · right
    right
    left
    exact ⟨L.image σ, hσ L hL, rfl⟩
  · right
    right
    right
    refine ⟨L.image σ, hσ L hL, ?_⟩
    show ((L.image σ)ᶜ, 0) = (Lᶜ.image σ, 0)
    rw [image_compl_perm]

theorem sideTerm_comp (σ : Perm (Fin 7)) (w : Fin 7 → ℕ) (hw : ∀ i, w i ≤ 5) (S : Finset (Fin 7)) (x : ℕ) :
    sideTerm (fun i => w (σ i)) (S, x) = sideTerm w (S.image σ, x) := by
  rw [sideTerm_eq _ (fun i => hw (σ i)), sideTerm_eq _ hw]
  congr 1
  rw [← Equiv.sum_comp σ (fun k => if k ∈ S.image σ then 5 - w k else w k)]
  refine sum_congr rfl fun i _ => ?_
  simp only [σ.injective.mem_finset_image]

/-- `M(v ∘ σ) = M(v)` for a collineation `σ`. -/
theorem M_comp {σ : Perm (Fin 7)} (hσ : IsColl σ) (v : Fin 7 → F16) : M (fun i => v (σ i)) = M v := by
  have hw : ∀ i, wpsi (v i) ≤ 5 := fun i => (wpsi_le _).trans (by norm_num)
  apply le_antisymm
  · obtain ⟨⟨S, x⟩, hSx, hM⟩ := exists_M_eq v
    have h1 := image_mem_e8Words (isColl_inv hσ) hSx
    have h2 : (S.image ⇑σ⁻¹).image ⇑σ = S := by
      rw [image_image, ← Perm.coe_mul, mul_inv_cancel, Perm.coe_one, image_id]
    calc M (fun i => v (σ i)) ≤ sideTerm (fun i => wpsi (v (σ i))) (S.image ⇑σ⁻¹, x) := M_le _ h1
      _ = sideTerm (fun i => wpsi (v i)) ((S.image ⇑σ⁻¹).image σ, x) :=
          sideTerm_comp σ (fun i => wpsi (v i)) hw _ _
      _ = M v := by rw [h2, hM]
  · obtain ⟨⟨S', x'⟩, hSx', hM'⟩ := exists_M_eq (fun i => v (σ i))
    calc M (fun i => v (σ i)) = sideTerm (fun i => wpsi (v (σ i))) (S', x') := hM'
      _ = sideTerm (fun i => wpsi (v i)) (S'.image σ, x') := sideTerm_comp σ (fun i => wpsi (v i)) hw _ _
      _ ≥ M v := M_le v (image_mem_e8Words hσ hSx')

end C72.T6O5
