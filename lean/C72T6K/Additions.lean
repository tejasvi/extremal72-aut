import C72T6K.Prop37

/-!
# T6, Klein part: further results

* `prop38_subgroup`: Proposition 3.8 in the paper's words, no subgroup of `Aut C` is isomorphic to `C₂ × C₂`.
* `prop37_converse_E`: the converse of Proposition 3.7 from the paper's solutions (one word from each orbit, the sets
  `E_{|y|}`).
* `Yof_map_swapP`: the last clause of Lemma 3.4 (b), the swap of pairs keeps the contracted fixed code.
* `noSol_iff_allRuledOut`, `allRuledOut_of_sub_slice`: the search hypothesis does not depend on the slice, and the
  slice of an echelon basis of any subspace of `G` suffices.
* `pair_form_fpf_needs_ab`: `pair_form_fpf` needs `a b` fixed-point-free (control T6C10).
-/

namespace C72.T6

open C72 C72.T4 Finset Equiv

/-- **Proposition 3.8** in the paper's form: under (L1), (L2), (L3), the representatives and the searches, no subgroup
of `Aut C` is isomorphic to `C₂ × C₂`. -/
theorem prop38_subgroup (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) (R : ∀ k : Fin 41, Set (Aut (Yc k)))
    (hR : ∀ (k : Fin 41) (β : Aut (Yc k)), IsFPFInv (β : Perm (Fin 36)) → ∃ g : Aut (Yc k), g⁻¹ * β * g ∈ R k)
    (hsearch : ∀ k : Fin 41, ∀ β ∈ R k, ∃ m : ℕ,
      ∃ E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m, ∀ B, ¬ IsSolK k β E B)
    (C : Code 72) (hC : Ext72 C) (V : Subgroup (Perm (Fin 72))) (hV : V ≤ Aut C) :
    IsEmpty (Multiplicative (ZMod 2 × ZMod 2) ≃* V) :=
  ⟨fun φ => prop38_of_searches hL1 hL2 hL3 R hR hsearch C hC _ _ (kleinPair_of_mulEquiv V hV φ)⟩

/-- **Proposition 3.7, backward, from the paper's solutions.** -/
theorem prop37_converse_E (k : Fin 41) (β : Aut (Yc k)) (hβ : IsFPFInv (β : Perm (Fin 36)))
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) (hB : InA (Yc k) (allOnes_mem_Yc k) β B) (R : Set (Yc k))
    (hR : ∀ y : Yc k, IsConstraint (y : Fin 36 → ZMod 2) → y ∈ R ∨ autLin β y ∈ R)
    (hnr : ¬ ∃ y ∈ R, IsConstraint (y : Fin 36 → ZMod 2) ∧ BadAtE (Yc k) B y) (h8 : MinWt (Yc k) 8) :
    TypeII (CB (Yc k) B) ∧ MinWt (CB (Yc k) B) 16 ∧ Yof (CB (Yc k) B) = Yc k ∧
      KleinPair (CB (Yc k) B) aStd (liftP (β : Perm (Fin 36))) ∧ (∀ p : Fin 36 × ZMod 2, aStd p ≠ p) ∧
      (∀ p, liftP (β : Perm (Fin 36)) p ≠ p) ∧
      ∀ p, ((aStd : Perm (Fin 36 × ZMod 2)) * liftP (β : Perm (Fin 36))) p ≠ p :=
  prop37_converse k β hβ B hB (fun h => hnr ((ruledOut_iff_reps_E (Yc_selfDual k) β hβ.1 hB R hR).1 h)) h8

/-- **Lemma 3.4 (b), last clause.** The swap of the coordinates of the pairs in `J` keeps the contracted fixed code. -/
theorem Yof_map_swapP {ι : Type*} [DecidableEq ι] (J : Finset ι) (C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)) :
    Yof (C.map (permute (swapP J)).toLinearMap) = Yof C := by
  ext u
  rw [mem_Yof, mem_Yof]
  constructor
  · rintro ⟨c, hc, hcu⟩
    have h : permute (swapP J) (permute (swapP J) c) = permute (swapP J) (pv u u) :=
      congrArg (fun x => permute (swapP J) x) hcu
    rw [permute_swapP_pv_self, ← permute_mul, swapP_mul_self, permute_one_apply] at h
    rw [← h]
    exact hc
  · intro hu
    exact ⟨pv u u, hu, permute_swapP_pv_self J u⟩

/-- The search hypothesis does not depend on the slice: no solution in one slice of `G` if and only if every form of
`A(Y_k, β)` is ruled out. -/
theorem noSol_iff_allRuledOut (k : Fin 41) (β : Aut (Yc k)) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m) :
    (∀ B, ¬ IsSolK k β E B) ↔ ∀ B, InA (Yc k) (allOnes_mem_Yc k) β B → RuledOut (Yc k) B := by
  constructor
  · intro h B hB
    by_contra hnr
    obtain ⟨B', hB'⟩ := exists_isSolK k β E hB hnr
    exact h B' hB'
  · rintro h B ⟨hA, -, hnr⟩
    exact hnr (h B hA)

/-- The slice of an echelon basis of any subspace `G' ≤ G` suffices (the program's `G` need not be all of `G`). -/
theorem allRuledOut_of_sub_slice (k : Fin 41) (β : Aut (Yc k))
    {G' : Submodule (ZMod 2) (LinearMap.BilinForm (ZMod 2) (Yc k))} (hG' : G' ≤ GK β) {m : ℕ}
    (E : EchelonBasis G' m)
    (h : ∀ B, InA (Yc k) (allOnes_mem_Yc k) β B → B ∈ slice E → RuledOut (Yc k) B) :
    ∀ B, InA (Yc k) (allOnes_mem_Yc k) β B → RuledOut (Yc k) B :=
  forall_of_slice E (fun _ hB _ hD => InA_add (Yc_selfDual k) hB (hG' hD))
    (fun B _ hD => ruledOut_add_iff B (GK_le_G0 β (hG' hD))) h

/-- **`pair_form_fpf` needs `a b` fixed-point-free.** `b = aStd` commutes with `aStd` and has no fixed point, but the
product `a b = aStd * aStd` fixes `(0, 0)` (it is the identity), and `b` has the form `(i, e) ↦ (β i, e + t i)` with
`β = 1` and `t = 1`, which has fixed points. -/
theorem pair_form_fpf_needs_ab :
    (aStd : Perm (Fin 2 × ZMod 2)) * aStd = aStd * aStd ∧ (∀ p : Fin 2 × ZMod 2, aStd p ≠ p) ∧
      (aStd * aStd : Perm (Fin 2 × ZMod 2)) (0, 0) = (0, 0) ∧
      (∀ (i : Fin 2) (e : ZMod 2), aStd (i, e) = ((1 : Perm (Fin 2)) i, e + 1)) ∧ (1 : Perm (Fin 2)) 0 = 0 := by
  refine ⟨rfl, ?_, by decide, fun i e => rfl, rfl⟩
  intro p hp
  have h := congrArg Prod.snd hp
  change p.2 + 1 = p.2 at h
  exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _ h

end C72.T6
