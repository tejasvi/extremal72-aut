import C72T1

/-!
# T4: relabelling codes along a bijection of index types

`reindex e` moves coordinate `i` of a word to coordinate `e i`, for a bijection `e : ι ≃ κ` between two finite index
types. For `ι = κ` it is T1's `permute`. Weight, dot product, duality, Type II and minimum weight are preserved, and
`CodeEquiv C D` says that some bijection of the coordinates maps `C` onto `D` (for `ι = κ = Fin n` this is T1's
`PermEquiv`). These facts are used to move the contracted fixed code, which lives on the orbits of an involution, to
`Fin 36`.
-/

namespace C72.T4

open C72 Module

variable {K : Type*} {ι κ μ : Type*}

/-- Relabelling along `e : ι ≃ κ`: `reindex e x = x ∘ e.symm`, so coordinate `i` of `x` becomes coordinate `e i`. -/
def reindex [Semiring K] (e : ι ≃ κ) : (ι → K) ≃ₗ[K] (κ → K) :=
  LinearEquiv.funCongrLeft K K e.symm

@[simp]
theorem reindex_apply [Semiring K] (e : ι ≃ κ) (x : ι → K) (k : κ) : reindex e x k = x (e.symm k) :=
  rfl

theorem reindex_apply_self [Semiring K] (e : ι ≃ κ) (x : ι → K) (i : ι) : reindex e x (e i) = x i := by
  simp

theorem reindex_perm [Semiring K] (p : Equiv.Perm ι) : reindex (K := K) p = permute p :=
  rfl

theorem reindex_trans_apply [Semiring K] (e : ι ≃ κ) (f : κ ≃ μ) (x : ι → K) :
    reindex (e.trans f) x = reindex f (reindex e x) :=
  rfl

theorem reindex_symm_apply [Semiring K] (e : ι ≃ κ) (x : ι → K) : reindex e.symm (reindex e x) = x := by
  funext i
  simp

theorem reindex_apply_symm [Semiring K] (e : ι ≃ κ) (y : κ → K) : reindex e (reindex e.symm y) = y := by
  funext k
  simp

theorem map_reindex_trans [Semiring K] (C : Submodule K (ι → K)) (e : ι ≃ κ) (f : κ ≃ μ) :
    (C.map (reindex e).toLinearMap).map (reindex f).toLinearMap = C.map (reindex (e.trans f)).toLinearMap := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨reindex e z, ⟨z, hz, rfl⟩, rfl⟩

theorem mem_map_reindex [Semiring K] {C : Submodule K (ι → K)} {e : ι ≃ κ} {y : κ → K} :
    y ∈ C.map (reindex e).toLinearMap ↔ reindex e.symm y ∈ C := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show reindex e.symm (reindex e x) ∈ C
    rw [reindex_symm_apply]
    exact hx
  · intro h
    exact ⟨reindex e.symm y, h, reindex_apply_symm e y⟩

theorem wt_reindex [Fintype ι] [Fintype κ] [Semiring K] [DecidableEq K] (e : ι ≃ κ) (x : ι → K) :
    wt (reindex e x) = wt x := by
  unfold wt hammingNorm
  refine Finset.card_bij (fun k _ => e.symm k) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_univ _, hk.2⟩
  · intro k _ l _ h
    exact e.symm.injective h
  · intro i hi
    rw [Finset.mem_filter] at hi
    refine ⟨e i, ?_, by simp⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hi.2⟩

theorem dotProduct_reindex [Fintype ι] [Fintype κ] [CommSemiring K] (e : ι ≃ κ) (x y : ι → K) :
    reindex e x ⬝ᵥ reindex e y = x ⬝ᵥ y := by
  simp only [dotProduct, reindex_apply]
  exact Equiv.sum_comp e.symm (fun i => x i * y i)

theorem dual_map_reindex [Fintype ι] [Fintype κ] [CommRing K] (C : Submodule K (ι → K)) (e : ι ≃ κ) :
    dual (C.map (reindex e).toLinearMap) = (dual C).map (reindex e).toLinearMap := by
  ext y
  rw [mem_map_reindex, mem_dual, mem_dual]
  constructor
  · intro h x hx
    have := h (reindex e x) ⟨x, hx, rfl⟩
    rw [← reindex_apply_symm e y, dotProduct_reindex] at this
    exact this
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← dotProduct_reindex e, reindex_apply_symm] at this
    exact this

theorem SelfDual.map_reindex [Fintype ι] [Fintype κ] [CommRing K] {C : Submodule K (ι → K)}
    (hC : SelfDual C) (e : ι ≃ κ) : SelfDual (C.map (reindex e).toLinearMap) := by
  unfold SelfDual at hC ⊢
  rw [dual_map_reindex, ← hC]

theorem TypeII.map_reindex [Fintype ι] [Fintype κ] {C : Submodule (ZMod 2) (ι → ZMod 2)} (hC : TypeII C)
    (e : ι ≃ κ) : TypeII (C.map (reindex e).toLinearMap) := by
  refine ⟨SelfDual.map_reindex hC.1 e, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  show 4 ∣ wt (reindex e x)
  rw [wt_reindex]
  exact hC.2 x hx

theorem MinWt.map_reindex [Fintype ι] [Fintype κ] {C : Submodule (ZMod 2) (ι → ZMod 2)} {d : ℕ}
    (hC : MinWt C d) (e : ι ≃ κ) : MinWt (C.map (reindex e).toLinearMap) d := by
  rintro _ ⟨x, hx, rfl⟩ hne
  show d ≤ wt (reindex e x)
  rw [wt_reindex]
  refine hC x hx ?_
  rintro rfl
  exact hne (map_zero _)

/-- Minimum weight exactly `d`. -/
def MinWtEq [Fintype ι] (C : Submodule (ZMod 2) (ι → ZMod 2)) (d : ℕ) : Prop :=
  MinWt C d ∧ ∃ x ∈ C, wt x = d

theorem MinWtEq.map_reindex [Fintype ι] [Fintype κ] {C : Submodule (ZMod 2) (ι → ZMod 2)} {d : ℕ}
    (hC : MinWtEq C d) (e : ι ≃ κ) : MinWtEq (C.map (reindex e).toLinearMap) d := by
  obtain ⟨h1, x, hx, hwx⟩ := hC
  exact ⟨MinWt.map_reindex h1 e, reindex e x, ⟨x, hx, rfl⟩, by rw [wt_reindex, hwx]⟩

/-- Two codes are equivalent if a bijection of their coordinates maps one onto the other. -/
def CodeEquiv [Semiring K] (C : Submodule K (ι → K)) (D : Submodule K (κ → K)) : Prop :=
  ∃ e : ι ≃ κ, C.map (reindex e).toLinearMap = D

theorem codeEquiv_iff_permEquiv [Semiring K] (C D : Submodule K (ι → K)) : CodeEquiv C D ↔ PermEquiv C D :=
  Iff.rfl

end C72.T4
