import C72T6.Gauge

/-!
# T6: the slice property and the bridge from the searches to `H_D`

A reduced echelon basis of a subspace `G` of forms is a family `D 0, …, D (m-1)` of elements of `G` spanning `G`, with
linear functionals ("pivot entries", for the program the Gram entries `B(w_a, w_b)`) `φ i` such that `φ i (D j) = δ_ij`.
The slice is the set of forms whose pivot entries vanish.

* **Slice property** (`slice_existsUnique`): every coset `B + G` meets the slice in exactly one form. For `G_0`: every
  coset of `G_0` in `A_0` meets `S_0 = A_0 ∩ slice` in exactly one form (`slice_A0_existsUnique`).
* With Lemma 3.5 (a) (`A_0` is a union of cosets of `G_0`) and Lemma 6.1 (b) (the condition `RuledOut` depends only on the
  coset), the claim of the order-2 search for `Y_k`, "every form of `S_0` is ruled out", gives `H_D k` (`H_D_of_slice`),
  for every echelon basis of `G_0`; the program uses the one whose pivots are the earliest Gram entries. Echelon bases
  exist (`exists_echelonBasis`, `exists_echelonBasis_G0`), so this hypothesis can always be met.
-/

namespace C72.T6

open C72 C72.T4 Module Finset

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A reduced echelon basis of `G`: `D j ∈ G` spanning `G`, and pivot functionals with `φ i (D j) = δ_ij`. -/
structure EchelonBasis (G : Submodule (ZMod 2) V) (m : ℕ) where
  D : Fin m → V
  φ : Fin m → V →ₗ[ZMod 2] ZMod 2
  mem : ∀ j, D j ∈ G
  spans : G ≤ Submodule.span (ZMod 2) (Set.range D)
  pivot : ∀ i j, φ i (D j) = if i = j then 1 else 0

variable {G : Submodule (ZMod 2) V} {m : ℕ}

/-- The slice: the forms whose pivot entries vanish. -/
def slice (E : EchelonBasis G m) : Set V :=
  {B | ∀ i, E.φ i B = 0}

/-- `∑_j c_j D_j` has pivot entries `c`. -/
theorem EchelonBasis.φ_sum (E : EchelonBasis G m) (c : Fin m → ZMod 2) (i : Fin m) :
    E.φ i (∑ j, c j • E.D j) = c i := by
  rw [map_sum]
  simp only [map_smul, E.pivot, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **Slice property.** Every coset `B + G` meets the slice in exactly one form. -/
theorem slice_existsUnique (E : EchelonBasis G m) (B : V) : ∃! D, D ∈ G ∧ B + D ∈ slice E := by
  refine ⟨∑ j, E.φ j B • E.D j, ⟨Submodule.sum_mem G (fun j _ => G.smul_mem _ (E.mem j)), fun i => ?_⟩, ?_⟩
  · rw [map_add, E.φ_sum]
    generalize E.φ i B = a
    revert a
    decide
  · rintro D' ⟨hD', hs⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (E.spans hD')
    have hci : ∀ i, c i = E.φ i B := by
      intro i
      have h := hs i
      rw [map_add, ← hc, E.φ_sum] at h
      generalize E.φ i B = a at h
      generalize c i = b at h
      revert a b
      decide
    rw [← hc]
    exact Finset.sum_congr rfl (fun j _ => by rw [hci j])

/-- The form of the slice in the coset `B + G`. -/
noncomputable def sliceRep (E : EchelonBasis G m) (B : V) : V :=
  B + ∑ j, E.φ j B • E.D j

theorem sliceRep_mem_slice (E : EchelonBasis G m) (B : V) : sliceRep E B ∈ slice E := by
  intro i
  rw [sliceRep, map_add, E.φ_sum]
  generalize E.φ i B = a
  revert a
  decide

theorem sliceRep_sub_mem (E : EchelonBasis G m) (B : V) : sliceRep E B - B ∈ G := by
  rw [sliceRep, add_sub_cancel_left]
  exact Submodule.sum_mem G (fun j _ => G.smul_mem _ (E.mem j))

/-- A property that is constant on cosets of `G` and holds on `A ∩ slice` holds on `A`, when `A` is a union of cosets. -/
theorem forall_of_slice (E : EchelonBasis G m) {A : V → Prop} (hA : ∀ B, A B → ∀ D ∈ G, A (B + D))
    {P : V → Prop} (hP : ∀ B, ∀ D ∈ G, P (B + D) ↔ P B) (h : ∀ B, A B → B ∈ slice E → P B) :
    ∀ B, A B → P B := by
  intro B hB
  have hD : sliceRep E B - B ∈ G := sliceRep_sub_mem E B
  have hrep : B + (sliceRep E B - B) = sliceRep E B := by abel
  have h1 := h (sliceRep E B) (by rw [← hrep]; exact hA B hB _ hD) (sliceRep_mem_slice E B)
  rw [← hrep] at h1
  exact (hP B _ hD).1 h1

/-- **From the search to `H_D`.** If every form of the slice `S_0(Y_k) = A_0(Y_k) ∩ slice` is ruled out (the claim of the
order-2 search for `Y_k`), then `H_D k`. -/
theorem H_D_of_slice (k : Fin 41) {m : ℕ} (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m)
    (h : ∀ B : LinearMap.BilinForm (ZMod 2) (Yc k), InA0 (Yc k) (allOnes_mem_Yc k) B → B ∈ slice E →
      RuledOut (Yc k) B) : H_D k :=
  (H_D_iff k).2 (forall_of_slice E (fun _ hB _ hD => InA0_add hB hD)
    (fun B _ hD => ruledOut_add_iff B hD) h)

/-- **Slice property for `S_0`.** For `B ∈ A_0(Y)` exactly one form of `S_0 = A_0 ∩ slice` lies in the coset `B + G_0`. -/
theorem slice_A0_existsUnique {ι : Type*} [Fintype ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)} {h1 : allOnes ∈ Y}
    {m : ℕ} (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) Y) (G0 Y) m) {B : LinearMap.BilinForm (ZMod 2) Y}
    (hB : InA0 Y h1 B) : ∃! B', (InA0 Y h1 B' ∧ B' ∈ slice E) ∧ B' - B ∈ G0 Y := by
  obtain ⟨D, ⟨hD, hs⟩, huniq⟩ := slice_existsUnique E B
  have hBD : B + D - B = D := by abel
  refine ⟨B + D, ⟨⟨InA0_add hB hD, hs⟩, by rw [hBD]; exact hD⟩, ?_⟩
  rintro B' ⟨⟨-, hs'⟩, hB'⟩
  have hrep : B + (B' - B) = B' := by abel
  have h := huniq (B' - B) ⟨hB', by rwa [hrep]⟩
  rw [← h, hrep]

/-- Every finite-dimensional `G` has a reduced echelon basis (a basis of `G` with its coordinate functionals extended to
`V`), so the hypothesis "`E` is an echelon basis of `G_0`" of the theorems here can always be met. -/
theorem exists_echelonBasis [FiniteDimensional (ZMod 2) G] : ∃ m, Nonempty (EchelonBasis G m) := by
  let b := Module.finBasis (ZMod 2) G
  choose φ hφ using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, ⟨{ D := fun j => (b j : V), φ := φ, mem := fun j => (b j).2, spans := ?_, pivot := ?_ }⟩⟩
  · intro x hx
    rw [Submodule.mem_span_range_iff_exists_fun (ZMod 2)]
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h
  · intro i j
    show φ i (b j : V) = if i = j then 1 else 0
    have h := LinearMap.congr_fun (hφ i) (b j)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]

/-- A subspace spanned by a finite set has an echelon basis. -/
theorem exists_echelonBasis_of_finite {s : Set V} (hs : s.Finite) (hG : G = Submodule.span (ZMod 2) s) :
    ∃ m, Nonempty (EchelonBasis G m) := by
  subst hG
  have : FiniteDimensional (ZMod 2) (Submodule.span (ZMod 2) s) := FiniteDimensional.span_of_finite (ZMod 2) hs
  exact exists_echelonBasis

/-- `G_0(Y)` has an echelon basis. -/
theorem exists_echelonBasis_G0 {ι : Type*} [Fintype ι] (Y : Submodule (ZMod 2) (ι → ZMod 2)) :
    ∃ m, Nonempty (EchelonBasis (V := LinearMap.BilinForm (ZMod 2) Y) (G0 Y) m) := by
  exact exists_echelonBasis_of_finite (V := LinearMap.BilinForm (ZMod 2) Y) (Set.finite_range (DT Y)) rfl

end C72.T6
