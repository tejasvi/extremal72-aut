import C72T2.Lemma42
import C72T1.Final
import C72T1.Labelling

/-!
# T2: Theorem B from four named hypotheses

**Theorem B.** A binary doubly-even self-dual `[72,36,16]` code has no automorphism of order 3.

Here `thmB_of : H_CP3 → H_Golay → H_LP → H_CB → ThmB`, with T1's `ThmB` (`orderOf g ≠ 3` for every `g ∈ Aut C`
of every `C` with `Ext72 C`). The four named hypotheses are `def … : Prop`, never axioms:

* `H_CP3` (cited, [CP82, Bou04]): an automorphism of order 3 has no fixed point;
* `H_Golay` (cited, uniqueness of the extended Golay code, used through [FN12, Lemma 3.1]);
* `H_LP` (cited, [MOSW78, LP90]): a Hermitian self-dual code of length 24 with minimum weight at least 8 has a
  word of weight 8;
* `H_CB` (computation): no Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid Golay code on its
  coordinates (Theorem C's classification together with the point-placement search, Section 4).

The proof is the paper's (Section 4): by `H_CP3` and T1's labelling lemma the automorphism is `sigma3` after a
relabelling; `G` is Type II with minimum weight at least 8, so `G = π(G24)` by `H_Golay`; `E` is Hermitian
self-dual with minimum weight at least 8, and has a word of weight 8 by `H_LP`; by the forward direction of
Lemma 4.2 the Golay code `π(G24)` is valid for `E` (`prop43_forward`, the forward direction of
Proposition 4.3), which `H_CB` excludes.
-/

namespace C72

open Equiv Finset F4 Three

/-! ## Valid Golay codes (Section 4.2 of the paper) -/

namespace Three

/-- An 8-subset `s` of the coordinates of `E` is forbidden if it meets the support of a word of weight 8 of `E`
in at least 7 points or lies in the support of a word of weight 10. -/
def Forbidden8 (E : Submodule F4 (Fin 24 → F4)) (s : Finset (Fin 24)) : Prop :=
  ∃ e ∈ E, (wt e = 8 ∧ 7 ≤ #(s ∩ supp e)) ∨ (wt e = 10 ∧ s ⊆ supp e)

/-- A 12-subset `s` is forbidden if it is the support of a word of weight 12 of `E`. -/
def Forbidden12 (E : Submodule F4 (Fin 24 → F4)) (s : Finset (Fin 24)) : Prop :=
  ∃ e ∈ E, wt e = 12 ∧ supp e = s

/-- The Golay code `π(G24)` on the coordinates of `E` (the image of `G24` under the bijection `π` from its points
to the coordinates of `E`) is valid for `E` if none of its octads `π(O)` and none of its dodecads `π(D)` is
forbidden. -/
def ValidGolay (E : Submodule F4 (Fin 24 → F4)) (π : Equiv.Perm (Fin 24)) : Prop :=
  (∀ O, IsOctad O → ¬ Forbidden8 E (O.map π.toEmbedding)) ∧
    ∀ D, IsDodecad D → ¬ Forbidden12 E (D.map π.toEmbedding)

/-- The support of `x π` is `π(supp x)`. -/
theorem supp_permute (π : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    supp (permute π x) = (supp x).map π.toEmbedding := by
  ext i
  rw [Finset.mem_map]
  constructor
  · intro h
    refine ⟨π.symm i, ?_, Equiv.apply_symm_apply π i⟩
    rw [mem_supp] at h ⊢
    simpa using h
  · rintro ⟨j, hj, rfl⟩
    rw [mem_supp] at hj ⊢
    simpa using hj

end Three

/-! ## Named hypotheses -/

/-- **H_CP3** (cited: Conway and Pless [CP82] and Bouyuklieva [Bou04]; see also [FN12, Sect. III] and
[Bor15, Prop. 6.1]): an automorphism of order 3 of a doubly-even self-dual `[72,36,16]` code has no fixed point,
so it has 24 cycles of length 3. Named hypothesis, not proved here. -/
def H_CP3 : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g = 3 → ∀ i, g i ≠ i

/-- **H_Golay** (cited: the uniqueness of the extended Golay code, used in the paper through [FN12, Lemma 3.1]):
a Type II code of length 24 with minimum weight at least 8 is equivalent to `G24`. Named hypothesis, not proved
here. -/
def H_Golay : Prop :=
  ∀ G : Code 24, TypeII G → MinWt G 8 → PermEquiv G G24

/-- **H_LP** (cited: `d ≤ 2⌊24/6⌋ + 2 = 10` [MOSW78], and there is no Hermitian self-dual `[24,12,10]` code
[LP90]): a Hermitian self-dual code of length 24 over `𝔽₄` with minimum weight at least 8 has a word of
weight 8. Named hypothesis, not proved here. -/
def H_LP : Prop :=
  ∀ E : Submodule F4 (Fin 24 → F4), HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) → ∃ e ∈ E, wt e = 8

/-- **H_CB** (computation: the classification of Theorem C together with the point-placement search of
Section 4): no Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid Golay code on its coordinates. For
every such code `E` and every bijection `π` from the points of `G24` to the coordinates of `E`, some octad `O`
of `G24` has an image `π(O)` that meets the support of a word of weight 8 of `E` in at least 7 points or lies in
the support of a word of weight 10, or some dodecad `D` has an image `π(D)` that is the support of a word of
weight 12. Named hypothesis, not proved here. -/
def H_CB : Prop :=
  ∀ E : Submodule F4 (Fin 24 → F4), HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) → (∃ e ∈ E, wt e = 8) →
    ∀ π : Equiv.Perm (Fin 24),
      (∃ O, IsOctad O ∧ ∃ e ∈ E, (wt e = 8 ∧ 7 ≤ #(O.map π.toEmbedding ∩ supp e)) ∨
          (wt e = 10 ∧ O.map π.toEmbedding ⊆ supp e)) ∨
        ∃ D, IsDodecad D ∧ ∃ e ∈ E, wt e = 12 ∧ supp e = D.map π.toEmbedding

/-- `H_CB` says exactly that no Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid Golay code. -/
theorem H_CB_iff : H_CB ↔ ∀ E : Submodule F4 (Fin 24 → F4), HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) →
    (∃ e ∈ E, wt e = 8) → ∀ π : Equiv.Perm (Fin 24), ¬ ValidGolay E π := by
  constructor
  · intro h E hE hE8 hEw π hval
    rcases h E hE hE8 hEw π with ⟨O, hO, hf⟩ | ⟨D, hD, hf⟩
    · exact hval.1 O hO hf
    · exact hval.2 D hD hf
  · intro h E hE hE8 hEw π
    by_contra hcon
    exact h E hE hE8 hEw π
      ⟨fun O hO hf => hcon (Or.inl ⟨O, hO, hf⟩), fun D hD hf => hcon (Or.inr ⟨D, hD, hf⟩)⟩

/-! ## Proposition 4.3, forward direction, and Theorem B -/

/-- **Proposition 4.3, forward direction.** If a doubly-even self-dual `[72,36,16]` code has an automorphism of
order 3, then some Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid Golay code on its coordinates
(from `H_CP3`, `H_Golay` and `H_LP`). -/
theorem prop43_forward (hCP3 : H_CP3) (hGolay : H_Golay) (hLP : H_LP) {C : Code 72} (hC : Ext72 C)
    {g : Perm (Fin 72)} (hg : g ∈ Aut C) (h3 : orderOf g = 3) :
    ∃ E : Submodule F4 (Fin 24 → F4), HSelfDual E ∧ (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) ∧ (∃ e ∈ E, wt e = 8) ∧
      ∃ π : Perm (Fin 24), ValidGolay E π := by
  have hfp := hCP3 C hC g hg h3
  obtain ⟨c, f, h, ρ, hf, hmem⟩ := exists_relabel Nat.prime_three hg h3
  have hf0 : f = 0 := by
    rw [hf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    exact hfp i
  subst hf0
  have hc : c = 24 := by omega
  subst hc
  have hσ : sigma3 ∈ Aut (C.map (permute ρ).toLinearMap) := hmem
  have hC' := hC.map_permute ρ
  have hE := Ecode_hselfDual hσ hC'.1.1
  have hE8 := Ecode_minWt hσ hC'.2.1
  obtain ⟨p, hp⟩ := hGolay _ (Gcode_typeII hσ hC'.1) (Gcode_minWt hC'.1.2 hC'.2.1)
  have hGeq : Gcode (C.map (permute ρ).toLinearMap) = G24.map (permute p⁻¹).toLinearMap := by
    rw [← hp, ← map_permute_mul, inv_mul_cancel, map_permute_one]
  have hfw := lemma42_forward (G := Gcode (C.map (permute ρ).toLinearMap))
    (E := Ecode (C.map (permute ρ).toLinearMap)) (by rw [Cof_Gcode_Ecode hσ]; exact hC'.2.1)
  refine ⟨_, hE, hE8, hLP _ hE hE8, p⁻¹, ?_, ?_⟩
  · rintro O ⟨x, hx, hx8, rfl⟩ ⟨e, he, hcase⟩
    have hy : permute p⁻¹ x ∈ Gcode (C.map (permute ρ).toLinearMap) := by
      rw [hGeq]
      exact Submodule.mem_map_of_mem hx
    have hy8 : wt (permute p⁻¹ x) = 8 := by
      rw [wt_permute, hx8]
    rcases hcase with ⟨he8, ht⟩ | ⟨he10, hsub⟩
    · have h6 := hfw.1 _ hy hy8 e he he8
      rw [supp_permute] at h6
      omega
    · exact hfw.2.1 _ hy hy8 e he he10 (by rw [supp_permute]; exact hsub)
  · rintro D ⟨x, hx, hx12, rfl⟩ ⟨e, he, he12, heq⟩
    have hy : permute p⁻¹ x ∈ Gcode (C.map (permute ρ).toLinearMap) := by
      rw [hGeq]
      exact Submodule.mem_map_of_mem hx
    have hy12 : wt (permute p⁻¹ x) = 12 := by
      rw [wt_permute, hx12]
    exact hfw.2.2 _ hy hy12 e he he12 (by rw [supp_permute]; exact heq)

/-- **Theorem B** from the named hypotheses `H_CP3`, `H_Golay`, `H_LP` and `H_CB`: a doubly-even self-dual
`[72,36,16]` code has no automorphism of order 3. -/
theorem thmB_of (hCP3 : H_CP3) (hGolay : H_Golay) (hLP : H_LP) (hCB : H_CB) : ThmB := by
  intro C hC g hg h3
  obtain ⟨E, hE, hE8, hEw, π, hval⟩ := prop43_forward hCP3 hGolay hLP hC hg h3
  exact (H_CB_iff.1 hCB) E hE hE8 hEw π hval

/-- T1's final deduction `main_of_cited` with `ThmB` replaced by its four named hypotheses. -/
theorem main_of_cited_thmB (h1 : H_primes) (hL1 : H_L1) (hA : ThmA) (hCP3 : H_CP3) (hGolay : H_Golay)
    (hLP : H_LP) (hCB : H_CB) (hD : NoFPFInv) : ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  main_of_cited h1 hL1 hA (thmB_of hCP3 hGolay hLP hCB) hD

end C72
