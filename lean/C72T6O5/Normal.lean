import C72T6O5.Scan

/-!
# T6 (order 5): Lemma 2.5, the normal form

**Lemma 2.5** (`lemma25`): every `7 × 7` matrix `U` over `𝔽₁₆` is mapped by the symmetries (a)-(c) (`Reach`) to a
matrix in normal form (`NormalForm`):

* (i) the row at depth 0 has the smallest key among all rows (`NFi`);
* (ii) the pattern of the row at depth 0 equals its key (`NFii`);
* (iii) every scanned entry that joins two different components of the graph built from the earlier entries is the
  representative of its norm class (`NFiii`).

The proof follows the paper: (b) on `A` gives (i), since the collineations are transitive on the points; (b) on `B`
and (c) give (ii), and they change no key; then the joining entries are normalised in scanning order
(`exists_NFiii_upto`; each position by `upto_succ`, using `normalise_joining`), which undoes no earlier normalisation
and changes no class, so (i) and (ii) are kept. The statement holds
for every matrix; as the symmetries preserve the conditions of Proposition 2.4 (`reach_sol`), a matrix as in
Proposition 2.4 is mapped to one in normal form that satisfies them as well (`lemma25_sol`).

`H_A_nf` is `H_A` restricted to matrices in normal form, and `H_A_iff_nf` shows that the two are equivalent: this is
the use of Lemma 2.5 in the proof of Proposition 2.4 ("a solution can be assumed to be in normal form").

The remark after Lemma 2.5: in normal form the row at depth 0 is determined by its key (`row0_eq_of_key`).
-/

namespace C72.T6O5

open C72.T3 Finset Equiv Matrix

/-- Property (i) of Lemma 2.5: the row at depth 0 has the smallest key among all rows. -/
def NFi (U : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  ∀ i, key (U (rowAt 0)) ≤ key (U i)

/-- Property (ii) of Lemma 2.5: the pattern of the row at depth 0 equals its key. -/
def NFii (U : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  pattern (U (rowAt 0)) = key (U (rowAt 0))

/-- The normal form of Lemma 2.5: properties (i), (ii) and (iii). -/
def NormalForm (U : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  NFi U ∧ NFii U ∧ NFiii U

instance (U : Matrix (Fin 7) (Fin 7) F16) : Decidable (NFi U) := by
  unfold NFi
  infer_instance

instance (U : Matrix (Fin 7) (Fin 7) F16) : Decidable (NFii U) := by
  unfold NFii
  infer_instance

/-- Property (iii) at the first `n` positions of the scan. -/
def NFiiiUpto (U : Matrix (Fin 7) (Fin 7) F16) (n : ℕ) : Prop :=
  ∀ i j, scanIdx i j < n → U i j ≠ 0 → Joins U i j → U i j = T3.Tests.clsRep (cls (U i j))

theorem NFiii_iff_upto (U : Matrix (Fin 7) (Fin 7) F16) : NFiii U ↔ NFiiiUpto U 49 :=
  ⟨fun h i j _ => h i j, fun h i j => h i j (scanIdx_lt i j)⟩

/-- Processing position `n` of the scan: if (iii) holds at the first `n` positions, then after the step of
`normalise_joining` (or none, if the entry at position `n` is zero or joins no components) it holds at the first
`n + 1` positions. No earlier normalisation is undone, and no class changes. -/
theorem upto_succ (V : Matrix (Fin 7) (Fin 7) F16) (n : ℕ) (hV : NFiiiUpto V n) :
    ∃ V', Reach V V' ∧ (∀ a b, cls (V' a b) = cls (V a b)) ∧ NFiiiUpto V' (n + 1) := by
  by_cases hex : ∃ i j, scanIdx i j = n ∧ V i j ≠ 0 ∧ Joins V i j
  · obtain ⟨i, j, hn, hij, hJ⟩ := hex
    obtain ⟨d₁, d₂, h₁, h₂, hrep, hearly, hcls'⟩ := normalise_joining V hij hJ
    refine ⟨(diagonal d₁)⁻¹ * V * diagonal d₂, reach_of_step (step_scale d₁ d₂ h₁ h₂ V), hcls', ?_⟩
    have hz : ∀ a b, V a b = 0 ↔ ((diagonal d₁)⁻¹ * V * diagonal d₂) a b = 0 := fun a b => by
      rw [← cls_eq_zero (V a b), ← cls_eq_zero (((diagonal d₁)⁻¹ * V * diagonal d₂) a b), hcls' a b]
    intro a b hab hne hJ'
    have hJV : Joins V a b := (joins_congr hz a b).2 hJ'
    have hne' : V a b ≠ 0 := fun h0 => hne ((hz a b).1 h0)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hlt | heq
    · rw [hearly a b hne' (by omega)]
      exact hV a b hlt hne' hJV
    · obtain ⟨rfl, rfl⟩ := scanIdx_inj (heq.trans hn.symm)
      rw [hcls']
      exact hrep
  · refine ⟨V, reach_refl V, fun _ _ => rfl, ?_⟩
    intro a b hab hne hJ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hlt | heq
    · exact hV a b hlt hne hJ
    · exact absurd ⟨a, b, heq, hne, hJ⟩ hex

/-- The joining entries are normalised in scanning order: after the first `n` positions of the scan, (iii) holds for
them, by symmetries (a) that change no class. -/
theorem exists_NFiii_upto (U : Matrix (Fin 7) (Fin 7) F16) (n : ℕ) :
    ∃ V, Reach U V ∧ (∀ a b, cls (V a b) = cls (U a b)) ∧ NFiiiUpto V n := by
  induction n with
  | zero => exact ⟨U, reach_refl U, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨V, hRV, hcls, hV⟩ := ih
    obtain ⟨V', hR', hcls', hV'⟩ := upto_succ V n hV
    exact ⟨V', reach_trans hRV hR', fun a b => (hcls' a b).trans (hcls a b), hV'⟩

/-- **Lemma 2.5.** Every matrix is mapped by the symmetries (a)-(c) to a matrix in normal form. -/
theorem lemma25 (U : Matrix (Fin 7) (Fin 7) F16) : ∃ V, Reach U V ∧ NormalForm V := by
  -- (i): a row of smallest key is moved to depth 0 by (b) on `A`
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image univ (fun i => key (U i)) univ_nonempty
  obtain ⟨σ, hσ, hσi₀⟩ := exists_isColl_apply_eq_zero i₀
  obtain ⟨V₁, hV₁⟩ : ∃ V₁, V₁ = (σ.permMatrix F16)⁻¹ * U * (1 : Perm (Fin 7)).permMatrix F16 := ⟨_, rfl⟩
  have hR₁ : Reach U V₁ := hV₁ ▸ reach_of_step (step_perm hσ isColl_one U)
  have hrow₁ : ∀ i, V₁ i = U (σ⁻¹ i) := fun i => funext fun j => by
    rw [hV₁]
    exact perm_apply σ 1 U i j
  have h0 : σ⁻¹ (rowAt 0) = i₀ := Perm.inv_eq_iff_eq.2 hσi₀.symm
  have hi₁ : ∀ i, key (V₁ (rowAt 0)) ≤ key (V₁ i) := fun i => by
    rw [hrow₁, hrow₁, h0]
    exact hi₀ _ (mem_univ _)
  -- (ii): (b) on `B` and possibly (c) make the pattern of the row at depth 0 its key
  obtain ⟨τ, hτ, e, hke⟩ := exists_key_eq (V₁ (rowAt 0))
  obtain ⟨V₂, hV₂⟩ : ∃ V₂, V₂ = ((1 : Perm (Fin 7)).permMatrix F16)⁻¹ * V₁ * τ⁻¹.permMatrix F16 := ⟨_, rfl⟩
  have hR₂ : Reach V₁ V₂ := hV₂ ▸ reach_of_step (step_perm isColl_one (isColl_inv hτ) V₁)
  have hV₂app : ∀ i j, V₂ i j = V₁ i (τ j) := fun i j => by
    rw [hV₂]
    exact perm_apply 1 τ⁻¹ V₁ i j
  obtain ⟨V₃, hR₃, hV₃⟩ : ∃ V₃, Reach V₂ V₃ ∧ ∀ i, V₃ i = img τ e (V₁ i) := by
    cases e
    · exact ⟨V₂, reach_refl _, fun i => funext fun j => hV₂app i j⟩
    · refine ⟨frobMat V₂, reach_of_step (step_frob V₂), fun i => funext fun j => ?_⟩
      show V₂ i j ^ 2 = V₁ i (τ j) ^ 2
      rw [hV₂app]
  have hkey₃ : ∀ i, key (V₃ i) = key (V₁ i) := fun i => by rw [hV₃, key_img hτ]
  have hi₃ : ∀ i, key (V₃ (rowAt 0)) ≤ key (V₃ i) := fun i => by
    rw [hkey₃, hkey₃]
    exact hi₁ i
  have hii₃ : pattern (V₃ (rowAt 0)) = key (V₃ (rowAt 0)) := by
    rw [hkey₃, hV₃]
    exact hke.symm
  -- (iii): the joining entries are normalised by (a), which changes no class
  obtain ⟨V, hR, hcls, hV⟩ := exists_NFiii_upto V₃ 49
  refine ⟨V, reach_trans hR₁ (reach_trans hR₂ (reach_trans hR₃ hR)), ?_, ?_, ?_⟩
  · intro i
    rw [key_congr (hcls (rowAt 0)), key_congr (hcls i)]
    exact hi₃ i
  · rw [NFii, pattern_congr (hcls (rowAt 0)), key_congr (hcls (rowAt 0))]
    exact hii₃
  · exact (NFiii_iff_upto V).2 hV

/-- Lemma 2.5 for a matrix as in Proposition 2.4: its normal form satisfies the conditions of Proposition 2.4. -/
theorem lemma25_sol {U : Matrix (Fin 7) (Fin 7) F16} (hU : Sol U) : ∃ V, Reach U V ∧ NormalForm V ∧ Sol V := by
  obtain ⟨V, hR, hV⟩ := lemma25 U
  exact ⟨V, hR, hV, reach_sol hR hU⟩

/-- `H_A` for matrices in normal form: no matrix in the normal form of Lemma 2.5 with `UU* = I` has
`M(a) + M(aU) ≥ 16` for every nonzero `a`. -/
def H_A_nf : Prop :=
  ∀ U : Matrix (Fin 7) (Fin 7) F16, NormalForm U → U * Uᴴ = 1 →
    ∃ a : Fin 7 → F16, a ≠ 0 ∧ M a + M (a ᵥ* U) < 16

/-- By Lemma 2.5, `H_A` follows from its restriction to matrices in normal form (and conversely). -/
theorem H_A_iff_nf : H_A ↔ H_A_nf := by
  constructor
  · intro h U _ hU
    exact h U hU
  · intro h
    rw [H_A_iff_forall_not_sol]
    intro U hU
    obtain ⟨V, -, hV, hsol⟩ := lemma25_sol hU
    obtain ⟨a, ha, hlt⟩ := h V hV hsol.1
    have := hsol.2 a ha
    omega

/-- In normal form the row at depth 0 is determined by its key: its entries are representatives (`row0_rep`), and by
(ii) its pattern, which gives the classes, is its key. -/
theorem row0_eq_of_key {U V : Matrix (Fin 7) (Fin 7) F16} (hU : NormalForm U) (hV : NormalForm V)
    (h : key (U (rowAt 0)) = key (V (rowAt 0))) : U (rowAt 0) = V (rowAt 0) := by
  have hUii : pattern (U (rowAt 0)) = key (U (rowAt 0)) := hU.2.1
  have hVii : pattern (V (rowAt 0)) = key (V (rowAt 0)) := hV.2.1
  have hp : pattern (U (rowAt 0)) = pattern (V (rowAt 0)) := by rw [hUii, hVii, h]
  funext j
  rw [row0_rep hU.2.2 j, row0_rep hV.2.2 j, cls_eq_of_pattern_eq hp j]

end C72.T6O5
