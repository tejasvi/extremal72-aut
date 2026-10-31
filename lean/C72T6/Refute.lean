import C72T6.Toy

/-!
# T6: refutations behind the controls

Each theorem shows that a hypothesis of a T6 theorem is needed. The control files `C72T6Controls/*.lean` state the
decidable core of the false variant and must fail.

* `lemma61b_needs_disjoint`: Lemma 6.1 (b) fails without disjointness (`D_{{0}}(1100, 1100) = 1` on `Y4`).
* `slice_needs_pivot`: the slice property fails without the pivot condition: for `G = span{11}` and `ψ(v) = v₀ + v₁`
  (`ψ(11) = 0`), the coset `10 + G` does not meet `{ψ = 0}`.
* `lemma63_needs_strict`: Lemma 6.3 fails with `K(B^g) ≤ K(B)` in place of `K(B^g) < K(B)`.
* `bits_need_leading`: the second test needs the leading bits; the bits below a position do not decide a comparison.
* `CB_doublyEven_needs_diag`: without (diag), `C_B` need not be doubly-even (`B = 0` on `Y4`).
* `CB_selfDual_needs_symm`: without symmetry, `C_B` need not be self-dual (`Bn` on `Y4`).
-/

namespace C72.T6.Refute

open C72 C72.T4 C72.T6 C72.T6.Toy

/-- The word `1100` of `Y4`. -/
def u1 : Y4 := ⟨![1, 1, 0, 0], mem_Y4.2 ⟨rfl, rfl⟩⟩

/-- The word `0011` of `Y4`. -/
def u2 : Y4 := ⟨![0, 0, 1, 1], mem_Y4.2 ⟨rfl, rfl⟩⟩

theorem DT_overlap : DT Y4 {0} u1 u1 = 1 := by
  rw [DT_apply]
  decide

/-- **Lemma 6.1 (b) needs disjointness.** -/
theorem lemma61b_needs_disjoint : ¬ ∀ D ∈ G0 Y4, ∀ y x : Y4, D y x = 0 := by
  intro h
  have h0 := h (DT Y4 {0}) (Submodule.subset_span ⟨{0}, rfl⟩) u1 u1
  rw [DT_overlap] at h0
  exact one_ne_zero h0

/-- The word `11`. -/
def d2 : Fin 2 → ZMod 2 := ![1, 1]

/-- `ψ(v) = v₀ + v₁`. -/
def ψ2 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v 0 + v 1
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem ψ2_apply (v : Fin 2 → ZMod 2) : ψ2 v = v 0 + v 1 :=
  rfl

/-- **The slice property needs the pivot condition.** `ψ(11) = 0` instead of `1`, and the coset `10 + span{11}` does not
meet `{ψ = 0}`. -/
theorem slice_needs_pivot : ψ2 d2 = 0 ∧ ¬ ∃ D ∈ Submodule.span (ZMod 2) {d2}, ψ2 (![1, 0] + D) = 0 := by
  refine ⟨by rw [ψ2_apply]; decide, ?_⟩
  rintro ⟨D, hD, h⟩
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hD
  clear hD
  rw [ψ2_apply] at h
  revert h
  revert t
  decide

/-- **Lemma 6.3 needs the strict decrease.** With `K(B^g) ≤ K(B)` in place of `K(B^g) < K(B)` the statement fails: two
forms swapped by `g`, both solutions, a constant key, each node a single form, every node removed. -/
theorem lemma63_needs_strict : ¬ ∀ (ext : Bool → Bool → Prop) (sol : Bool → Prop) (removed : Bool → Prop)
    (act : Bool → Bool → Bool) (K : Bool → ℕ) (rep : Bool → Bool),
    (∀ g B, sol B → sol (rep (act g B))) → (∀ g B, K (rep (act g B)) = K (act g B)) →
    (∀ n, removed n → (∀ B, ext B n → ¬ sol B) ∨ ∃ g, ∀ B, ext B n → K (act g B) ≤ K B) →
    (∃ B, sol B) → ∃ B, sol B ∧ ∀ n, ext B n → ¬ removed n := by
  intro h
  obtain ⟨B, -, hB⟩ := h (fun B n => B = n) (fun _ => True) (fun _ => True) (fun g B => Bool.xor g B) (fun _ => 0) id
    (fun _ _ _ => trivial) (fun _ _ => rfl) (fun _ _ => Or.inr ⟨true, fun _ _ => le_refl 0⟩) ⟨false, trivial⟩
  exact hB B rfl trivial

/-- **The second test needs the leading bits.** The bits below position `t` do not decide a comparison. -/
theorem bits_need_leading : ¬ ∀ a b t : ℕ, a % 2 ^ t < b % 2 ^ t → a < b := by
  intro h
  exact absurd (h 4 1 2 (by decide)) (by decide)

/-- **`CB_doublyEven` needs (diag).** `B = 0` violates (diag) at `1100`, and `C_0` contains `(0000 | 1100)` of weight 2. -/
theorem CB_doublyEven_needs_diag :
    ¬ (∀ y : Y4, (0 : LinearMap.BilinForm (ZMod 2) Y4) y y =
      ((wt (y : Fin 4 → ZMod 2) / 2 : ℕ) : ZMod 2) + (0 : LinearMap.BilinForm (ZMod 2) Y4) y ⟨allOnes, allOnes_mem_Y4⟩) ∧
    pv 0 (u1 : Fin 4 → ZMod 2) ∈ CB Y4 0 ∧ ¬ 4 ∣ wt (pv 0 (u1 : Fin 4 → ZMod 2)) := by
  refine ⟨fun h => ?_, mem_CB.2 ⟨u1, 0, fun y' => ?_, ?_⟩, by decide⟩
  · have h0 := h u1
    simp only [LinearMap.zero_apply, add_zero] at h0
    revert h0
    decide
  · simp only [zero_dotProduct, LinearMap.zero_apply]
  · rw [zero_add]

/-- The word `0010`. -/
def z1 : Fin 4 → ZMod 2 := ![0, 0, 1, 0]

/-- **`CB_selfDual` needs symmetry.** `Bn(1100, 0011) ≠ Bn(0011, 1100)`, and the words `(0010 | 1110)` and `(0000 | 0011)`
of `C_{Bn}` are not orthogonal, so `C_{Bn}` is not self-dual. -/
theorem CB_selfDual_needs_symm : Bn u1 u2 ≠ Bn u2 u1 ∧ pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ∈ CB Y4 Bn ∧
    pv 0 (0 + (u2 : Fin 4 → ZMod 2)) ∈ CB Y4 Bn ∧
    pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ⬝ᵥ pv 0 (0 + (u2 : Fin 4 → ZMod 2)) ≠ 0 ∧ ¬ SelfDual (CB Y4 Bn) := by
  have h1 : pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ∈ CB Y4 Bn := by
    refine mem_CB.2 ⟨u1, z1, fun y' => ?_, rfl⟩
    show z1 ⬝ᵥ (y' : Fin 4 → ZMod 2) = (u1 : Fin 4 → ZMod 2) 0 * (y' : Fin 4 → ZMod 2) 2
    rw [dot_four]
    simp [z1, u1]
  have h2 : pv 0 (0 + (u2 : Fin 4 → ZMod 2)) ∈ CB Y4 Bn := by
    refine mem_CB.2 ⟨u2, 0, fun y' => ?_, rfl⟩
    show (0 : Fin 4 → ZMod 2) ⬝ᵥ (y' : Fin 4 → ZMod 2) = (u2 : Fin 4 → ZMod 2) 0 * (y' : Fin 4 → ZMod 2) 2
    rw [zero_dotProduct]
    simp [u2]
  have h3 : pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ⬝ᵥ pv 0 (0 + (u2 : Fin 4 → ZMod 2)) ≠ 0 := by decide
  have h4 : Bn u1 u2 ≠ Bn u2 u1 := by
    show (u1 : Fin 4 → ZMod 2) 0 * (u2 : Fin 4 → ZMod 2) 2 ≠ (u2 : Fin 4 → ZMod 2) 0 * (u1 : Fin 4 → ZMod 2) 2
    decide
  refine ⟨h4, h1, h2, h3, fun hsd => h3 ?_⟩
  have h1' : pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ∈ dual (CB Y4 Bn) := by
    rw [← hsd]
    exact h1
  exact (mem_dual.1 h1') _ h2

end C72.T6.Refute
