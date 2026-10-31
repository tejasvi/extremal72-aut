import C72T6O5.Sym

/-!
# T6 (order 5): patterns and keys of rows (Sec. 2.4)

* The pattern of `v ∈ 𝔽₁₆⁷` is the vector of norm classes of its entries (`0` for a zero entry), read as the base-4
  integer `Σ_j c_j 4^j` (`pattern`). It depends only on the classes (`pattern_congr`) and determines them
  (`cls_eq_of_pattern_eq`).
* The images of a row under the collineations (acting on the columns, as in (b) on `B`) and the Frobenius map are the
  rows `img σ e v : j ↦ v (σ j)`, squared if `e` (`img`). The key of `v` is the smallest pattern among them (`key`,
  a minimum over the 168 tables `tableOf a b c` and `e ∈ {false, true}`). It is the minimum over the whole orbit of
  `v` under the collineations and all powers of the Frobenius map (`key_le_orbit`, `exists_orbit_eq_key`); the
  Frobenius map fixes class 1 and interchanges classes 2 and 3 (`cls_sq`).
* The key is unchanged by the collineations, the Frobenius map, and any change of the entries that keeps their classes,
  for example a scaling by `μ₅` (`key_comp`, `key_frob`, `key_img`, `key_congr`).
-/

namespace C72.T6O5

open C72.T3 Finset Equiv

/-- The pattern of `v` (Sec. 2.4): the norm classes `c_j` of the entries read as the base-4 integer `Σ_j c_j 4^j`. -/
def pattern (v : Fin 7 → F16) : ℕ :=
  ∑ j : Fin 7, cls (v j) * 4 ^ (j : ℕ)

/-- The image of the row `v` under the collineation with table `f` and, if `e`, the Frobenius map `y ↦ y²`. -/
def img (f : Fin 7 → Fin 7) (e : Bool) (v : Fin 7 → F16) : Fin 7 → F16 :=
  fun j => if e then v (f j) ^ 2 else v (f j)

theorem ncTriples_nonempty : ncTriples.Nonempty :=
  ⟨(0, 1, 2), mem_ncTriples.2 (by decide +kernel)⟩

/-- The key of the row `v` (Sec. 2.4): the smallest pattern among its images under the collineations and the
Frobenius map. The tables `tableOf a b c` over `ncTriples` are exactly the collineations (`collEquiv`). -/
def key (v : Fin 7 → F16) : ℕ :=
  ncTriples.inf' ncTriples_nonempty fun p =>
    min (pattern (img (tableOf p.1 p.2.1 p.2.2) false v)) (pattern (img (tableOf p.1 p.2.1 p.2.2) true v))

theorem key_le {σ : Perm (Fin 7)} (hσ : IsColl σ) (e : Bool) (v : Fin 7 → F16) : key v ≤ pattern (img σ e v) := by
  have h := inf'_le (fun p : Fin 7 × Fin 7 × Fin 7 =>
    min (pattern (img (tableOf p.1 p.2.1 p.2.2) false v)) (pattern (img (tableOf p.1 p.2.1 p.2.2) true v)))
    ((mem_ncTriples (p := (σ 0, σ 1, σ 2))).2 (nc_of_isColl hσ))
  rw [coe_eq_tableOf hσ]
  refine h.trans ?_
  cases e
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem exists_key_eq (v : Fin 7 → F16) : ∃ σ : Perm (Fin 7), IsColl σ ∧ ∃ e : Bool, key v = pattern (img σ e v) := by
  obtain ⟨⟨a, b, c⟩, hp, hk⟩ := exists_mem_eq_inf' ncTriples_nonempty (fun p : Fin 7 × Fin 7 × Fin 7 =>
    min (pattern (img (tableOf p.1 p.2.1 p.2.2) false v)) (pattern (img (tableOf p.1 p.2.1 p.2.2) true v)))
  have h : NC a b c := mem_ncTriples.1 hp
  rcases min_choice (pattern (img (tableOf a b c) false v)) (pattern (img (tableOf a b c) true v)) with hm | hm
  · exact ⟨collOf a b c h, isColl_collOf h, false, hk.trans hm⟩
  · exact ⟨collOf a b c h, isColl_collOf h, true, hk.trans hm⟩

theorem key_le_pattern (v : Fin 7 → F16) : key v ≤ pattern v :=
  key_le isColl_one false v

/-! ## The classes under the Frobenius map -/

/-- The Frobenius map on the classes: it fixes `0` and `1` and interchanges `2` and `3`. -/
def frobCls (c : ℕ) : ℕ :=
  if c = 2 then 3 else if c = 3 then 2 else c

/-- The Frobenius map fixes class 1 and interchanges classes 2 and 3 (Sec. 2.4). -/
theorem cls_sq : ∀ y : F16, cls (y ^ 2) = frobCls (cls y) := by decide +kernel

theorem frobCls_frobCls (c : ℕ) : frobCls (frobCls c) = c := by
  unfold frobCls
  split_ifs <;> omega

theorem cls_pow_two_pow (n : ℕ) (y : F16) : cls (y ^ (2 ^ n)) = if n % 2 = 0 then cls y else frobCls (cls y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, cls_sq, ih]
    by_cases h : n % 2 = 0
    · rw [ite_eq_left h, ite_eq_right (by omega)]
    · rw [ite_eq_right h, ite_eq_left (by omega), frobCls_frobCls]

/-! ## Patterns -/

theorem pattern_congr {v w : Fin 7 → F16} (h : ∀ j, cls (v j) = cls (w j)) : pattern v = pattern w := by
  unfold pattern
  exact sum_congr rfl fun j _ => by rw [h j]

/-- The pattern determines the classes of the entries (base-4 digits). -/
theorem cls_eq_of_pattern_eq {v w : Fin 7 → F16} (h : pattern v = pattern w) (j : Fin 7) : cls (v j) = cls (w j) := by
  simp only [pattern, Fin.sum_univ_seven, Fin.val_zero, Fin.val_one, Fin.val_two] at h
  have hv0 := cls_lt (v 0)
  have hv1 := cls_lt (v 1)
  have hv2 := cls_lt (v 2)
  have hv3 := cls_lt (v 3)
  have hv4 := cls_lt (v 4)
  have hv5 := cls_lt (v 5)
  have hv6 := cls_lt (v 6)
  have hw0 := cls_lt (w 0)
  have hw1 := cls_lt (w 1)
  have hw2 := cls_lt (w 2)
  have hw3 := cls_lt (w 3)
  have hw4 := cls_lt (w 4)
  have hw5 := cls_lt (w 5)
  have hw6 := cls_lt (w 6)
  have h' : cls (v 0) = cls (w 0) ∧ cls (v 1) = cls (w 1) ∧ cls (v 2) = cls (w 2) ∧ cls (v 3) = cls (w 3) ∧
      cls (v 4) = cls (w 4) ∧ cls (v 5) = cls (w 5) ∧ cls (v 6) = cls (w 6) := by
    norm_num at h
    omega
  fin_cases j
  exacts [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2]

theorem cls_img_congr {v w : Fin 7 → F16} (h : ∀ j, cls (v j) = cls (w j)) (f : Fin 7 → Fin 7) (e : Bool)
    (j : Fin 7) : cls (img f e v j) = cls (img f e w j) := by
  cases e
  · exact h (f j)
  · show cls (v (f j) ^ 2) = cls (w (f j) ^ 2)
    rw [cls_sq, cls_sq, h]

/-! ## Invariance of the key -/

/-- The key depends only on the classes of the entries. -/
theorem key_congr {v w : Fin 7 → F16} (h : ∀ j, cls (v j) = cls (w j)) : key v = key w := by
  unfold key
  congr 1
  funext p
  exact congrArg₂ min (pattern_congr (cls_img_congr h _ _)) (pattern_congr (cls_img_congr h _ _))

/-- A collineation of the columns does not change the key. -/
theorem key_comp {σ : Perm (Fin 7)} (hσ : IsColl σ) (v : Fin 7 → F16) : key (fun j => v (σ j)) = key v := by
  apply le_antisymm
  · obtain ⟨τ, hτ, e, hk⟩ := exists_key_eq v
    have himg : (img ⇑(σ⁻¹ * τ) e fun j => v (σ j)) = img τ e v := by
      funext j
      simp only [img, Perm.mul_apply, perm_apply_inv_self]
    calc key (fun j => v (σ j)) ≤ pattern (img ⇑(σ⁻¹ * τ) e fun j => v (σ j)) :=
          key_le (isColl_mul (isColl_inv hσ) hτ) e _
      _ = key v := by rw [himg, hk]
  · obtain ⟨τ, hτ, e, hk⟩ := exists_key_eq (fun j => v (σ j))
    calc key v ≤ pattern (img ⇑(σ * τ) e v) := key_le (isColl_mul hσ hτ) e v
      _ = pattern (img τ e fun j => v (σ j)) := rfl
      _ = key (fun j => v (σ j)) := hk.symm

/-- The Frobenius map does not change the key. -/
theorem key_frob (v : Fin 7 → F16) : key (fun j => v j ^ 2) = key v := by
  have h1 : ∀ f e, pattern (img f e fun j => v j ^ 2) = pattern (img f (!e) v) := by
    intro f e
    apply pattern_congr
    intro j
    cases e
    · rfl
    · show cls ((v (f j) ^ 2) ^ 2) = cls (v (f j))
      rw [cls_sq, cls_sq, frobCls_frobCls]
  apply le_antisymm
  · obtain ⟨τ, hτ, e, hk⟩ := exists_key_eq v
    calc key (fun j => v j ^ 2) ≤ pattern (img τ (!e) fun j => v j ^ 2) := key_le hτ _ _
      _ = key v := by rw [h1, Bool.not_not, hk]
  · obtain ⟨τ, hτ, e, hk⟩ := exists_key_eq (fun j => v j ^ 2)
    calc key v ≤ pattern (img τ (!e) v) := key_le hτ _ _
      _ = pattern (img τ e fun j => v j ^ 2) := (h1 τ e).symm
      _ = key (fun j => v j ^ 2) := hk.symm

theorem key_img {σ : Perm (Fin 7)} (hσ : IsColl σ) (e : Bool) (v : Fin 7 → F16) : key (img σ e v) = key v := by
  cases e
  · exact key_comp hσ v
  · exact (key_frob fun j => v (σ j)).trans (key_comp hσ v)

/-- The key is at most the pattern of every image of `v` under a collineation and a power of the Frobenius map. -/
theorem key_le_orbit {σ : Perm (Fin 7)} (hσ : IsColl σ) (n : ℕ) (v : Fin 7 → F16) :
    key v ≤ pattern (fun j => v (σ j) ^ (2 ^ n)) := by
  have h : pattern (fun j => v (σ j) ^ (2 ^ n)) = pattern (img σ (decide (n % 2 = 1)) v) := by
    apply pattern_congr
    intro j
    rw [cls_pow_two_pow]
    by_cases hn : n % 2 = 0
    · rw [ite_eq_left hn]
      have hd : decide (n % 2 = 1) = false := decide_eq_false (by omega)
      simp only [img, hd]
      rfl
    · rw [ite_eq_right hn]
      have hd : decide (n % 2 = 1) = true := decide_eq_true (by omega)
      simp only [img, hd, ite_true]
      rw [cls_sq]
  rw [h]
  exact key_le hσ _ v

/-- The key is the pattern of an image of `v` under a collineation and the Frobenius map or the identity. -/
theorem exists_orbit_eq_key (v : Fin 7 → F16) :
    ∃ σ : Perm (Fin 7), IsColl σ ∧ ∃ n : ℕ, n < 2 ∧ key v = pattern (fun j => v (σ j) ^ (2 ^ n)) := by
  obtain ⟨σ, hσ, e, hk⟩ := exists_key_eq v
  refine ⟨σ, hσ, if e then 1 else 0, by split_ifs <;> omega, ?_⟩
  have himg : img σ e v = fun j => v (σ j) ^ (2 ^ (if e then 1 else 0)) := by
    funext j
    cases e <;> simp [img]
  rw [hk, himg]

/-! ## The key computed from the classes -/

/-- The pattern of a vector of classes. -/
def patC (c : Fin 7 → ℕ) : ℕ :=
  ∑ j : Fin 7, c j * 4 ^ (j : ℕ)

/-- The key computed from the vector of classes, with the Frobenius map acting on the classes by `frobCls`
(`key_eq_keyC`). -/
def keyC (c : Fin 7 → ℕ) : ℕ :=
  ncTriples.inf' ncTriples_nonempty fun p =>
    min (patC fun j => c (tableOf p.1 p.2.1 p.2.2 j)) (patC fun j => frobCls (c (tableOf p.1 p.2.1 p.2.2 j)))

theorem pattern_eq_patC (v : Fin 7 → F16) : pattern v = patC fun j => cls (v j) :=
  rfl

theorem key_eq_keyC (v : Fin 7 → F16) : key v = keyC fun j => cls (v j) := by
  unfold key keyC
  congr 1
  funext p
  refine congrArg₂ min rfl ?_
  unfold pattern patC
  refine sum_congr rfl fun j _ => ?_
  show cls (v (tableOf p.1 p.2.1 p.2.2 j) ^ 2) * 4 ^ (j : ℕ) =
    frobCls (cls (v (tableOf p.1 p.2.1 p.2.2 j))) * 4 ^ (j : ℕ)
  rw [cls_sq]

end C72.T6O5
