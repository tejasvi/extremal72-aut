import C72T2.Reduction
import C72T2.Golay

/-!
# T2: Lemma 4.2 of the paper (the distance condition)

Let `G ≤ 𝔽₂²⁴` and let `E ≤ 𝔽₄²⁴` be `𝔽₄`-linear, and let `C = {g^{(3)} : g ∈ G} ⊕ φ(E)` (`Cof G E`). The words
of weight 8 and 12 of `G` are its octads and dodecads.

* (W8) every support of a word of weight 8 of `E` meets every octad in at most 6 points;
* (W10) no support of a word of weight 10 of `E` contains an octad;
* (W12) no support of a word of weight 12 of `E` is a dodecad.

**Lemma 4.2.** If `G` is equivalent to the extended Golay code and `E` is Hermitian self-dual with minimum
distance at least 8, then `C` has minimum weight at least 16 if and only if (W8), (W10) and (W12) hold
(`lemma42`). The forward direction holds for all `G` and `E` (`lemma42_forward`): a word violating (W8), (W10)
or (W12) gives a nonzero word of `C` of weight at most 12, by Lemma 4.1. The converse uses the weights
`0, 8, 12, 16, 24` of `G24` (`G24_wt`) and the even weights of `E`.
-/

namespace C72.Three

open Equiv Finset F4

/-- (W8): every support of a word of weight 8 of `E` meets every octad of `G` in at most 6 points. -/
def W8 (G : Code 24) (E : Submodule F4 (Fin 24 → F4)) : Prop :=
  ∀ g ∈ G, wt g = 8 → ∀ e ∈ E, wt e = 8 → #(supp g ∩ supp e) ≤ 6

/-- (W10): no support of a word of weight 10 of `E` contains an octad of `G`. -/
def W10 (G : Code 24) (E : Submodule F4 (Fin 24 → F4)) : Prop :=
  ∀ g ∈ G, wt g = 8 → ∀ e ∈ E, wt e = 10 → ¬ supp g ⊆ supp e

/-- (W12): no support of a word of weight 12 of `E` is a dodecad of `G`. -/
def W12 (G : Code 24) (E : Submodule F4 (Fin 24 → F4)) : Prop :=
  ∀ g ∈ G, wt g = 12 → ∀ e ∈ E, wt e = 12 → supp e ≠ supp g

theorem subset_of_card_inter {s t : Finset (Fin 24)} (h : #(s ∩ t) = #s) : s ⊆ t :=
  Finset.inter_eq_left.1 (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq h.symm))

/-- **Lemma 4.2, forward direction**, for any `G` and `E`. -/
theorem lemma42_forward {G : Code 24} {E : Submodule F4 (Fin 24 → F4)} (h : MinWt (Cof G E) 16) :
    W8 G E ∧ W10 G E ∧ W12 G E := by
  have key : ∀ g ∈ G, ∀ e ∈ E, 0 < wt (triple g + phi e) → 16 ≤ wt (triple g + phi e) := by
    intro g hg e he hpos
    refine h _ ⟨g, hg, e, he, rfl⟩ (fun h0 => ?_)
    rw [h0, wt_zero] at hpos
    exact lt_irrefl 0 hpos
  have htg : ∀ (g : Fin 24 → ZMod 2) (e : Fin 24 → F4), #(supp g ∩ supp e) ≤ wt g := fun g e =>
    Finset.card_le_card Finset.inter_subset_left
  refine ⟨fun g hg hg8 e he he8 => ?_, fun g hg hg8 e he he10 hsub => ?_,
    fun g hg hg12 e he he12 heq => ?_⟩
  · have h41 := lemma41 g e
    have h1 := htg g e
    by_contra hcon
    have := key g hg e he (by omega)
    omega
  · have ht : #(supp g ∩ supp e) = 8 := by
      rw [Finset.inter_eq_left.2 hsub, card_supp, hg8]
    have h41 := lemma41 g e
    have := key g hg e he (by omega)
    omega
  · have ht : #(supp g ∩ supp e) = 12 := by
      rw [heq, Finset.inter_self, card_supp, hg12]
    have h41 := lemma41 g e
    have := key g hg e he (by omega)
    omega

/-- **Lemma 4.2, converse direction.** -/
theorem lemma42_converse {G : Code 24} (hG : PermEquiv G24 G) {E : Submodule F4 (Fin 24 → F4)}
    (hE : HSelfDual E) (hE8 : ∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) (h8 : W8 G E) (h10 : W10 G E) (h12 : W12 G E) :
    MinWt (Cof G E) 16 := by
  obtain ⟨p, rfl⟩ := hG
  rintro _ ⟨g, hg, e, he, rfl⟩ hne
  have hgw : wt g = 0 ∨ wt g = 8 ∨ wt g = 12 ∨ wt g = 16 ∨ wt g = 24 := by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hg
    rw [show (permute p).toLinearMap x = permute p x from rfl, wt_permute]
    exact G24_wt hx
  obtain ⟨m, hm⟩ := hE.even_wt he
  have hle : wt e ≤ 24 := by
    have := wt_le_card e
    rwa [Fintype.card_fin] at this
  have h41 := lemma41 g e
  have htg : #(supp g ∩ supp e) ≤ wt g := Finset.card_le_card Finset.inter_subset_left
  have hte : #(supp g ∩ supp e) ≤ wt e := Finset.card_le_card Finset.inter_subset_right
  by_cases he0 : e = 0
  · subst he0
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hne
      rw [map_zero, phi_zero, add_zero]
    have hgw0 : wt g ≠ 0 := fun h => hg0 (wt_eq_zero.1 h)
    rw [wt_zero] at h41 hte
    omega
  have he8 := hE8 e he he0
  by_cases hg0 : g = 0
  · subst hg0
    rw [wt_zero] at htg h41
    omega
  rcases hgw with hw | hw | hw | hw | hw
  · exact absurd (wt_eq_zero.1 hw) hg0
  · rcases (show wt e = 8 ∨ wt e = 10 ∨ 12 ≤ wt e by omega) with hw' | hw' | hw'
    · have := h8 g hg hw e he hw'
      omega
    · have : #(supp g ∩ supp e) ≠ 8 := fun ht =>
        h10 g hg hw e he hw' (subset_of_card_inter (by rw [ht, card_supp, hw]))
      omega
    · omega
  · by_cases hw' : wt e = 12
    · have : #(supp g ∩ supp e) ≠ 12 := fun ht => by
        have hsub := subset_of_card_inter (by rw [ht, card_supp, hw])
        have hsg : supp g = supp e :=
          Finset.eq_of_subset_of_card_le hsub (by rw [card_supp, card_supp, hw, hw'])
        exact h12 g hg hw e he hw' hsg.symm
      omega
    · omega
  · omega
  · have hsg : supp g = univ := Finset.eq_univ_of_card _ (by rw [card_supp, hw, Fintype.card_fin])
    have ht : #(supp g ∩ supp e) = wt e := by
      rw [hsg, Finset.univ_inter, card_supp]
    omega

/-- **Lemma 4.2.** Let `G` be equivalent to the extended Golay code and let `E` be a Hermitian self-dual code
over `𝔽₄` of length 24 with minimum distance at least 8. Then `C = {g^{(3)} : g ∈ G} ⊕ φ(E)` has minimum
weight at least 16 if and only if (W8), (W10) and (W12) hold. -/
theorem lemma42 {G : Code 24} (hG : PermEquiv G24 G) {E : Submodule F4 (Fin 24 → F4)} (hE : HSelfDual E)
    (hE8 : ∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) :
    MinWt (Cof G E) 16 ↔ W8 G E ∧ W10 G E ∧ W12 G E :=
  ⟨lemma42_forward, fun h => lemma42_converse hG hE hE8 h.1 h.2.1 h.2.2⟩

end C72.Three
