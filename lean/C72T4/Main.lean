import C72T4.Relabel
import C72T4.Lemma32
import C72T4.Lemma36

/-!
# T4: Theorem D and "no involution"

* `thmD_of_HD k`: Theorem D for `Y_k` from the search hypothesis `H_D k` alone. The self-duality of `Y_k` needed for
  the model is proved from the data (`Yc_selfDual`), so (L2) is not used here.
* `noFPFInv_of`: no extremal code has a fixed-point-free involution, from `H_L2`, `H_L3` and all `H_D k` (the step
  "by (L2), (L3) and Theorem D" of the paper's proof of the Main Theorem). This is T1's named hypothesis `NoFPFInv`.
* `noInv_of_T4`: no involution at all, with `H_L1` (T1's `noInv_of`).
* `main_of_T4`: T1's final deduction with this result in place of `NoInv`.

Proof of `thmD_of_HD`: relabel the coordinates as pairs so that the involution is `aStd` and the contracted fixed code
is `Y_k` (`pairEquiv`); write the code as `C_B` with `B ∈ A_0(Y_k)` (`model`); `H_D k` gives a constraint word whose
syndrome is a bad pattern, and Lemma 3.6 (`lemma36`) gives a nonzero word of weight below 16.
-/

namespace C72.T4

open C72 Module Finset Equiv

theorem mul_self_eq_one_of_orderOf_two {ι : Type*} {a : Perm ι} (ha : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← ha, pow_orderOf_eq_one]

/-- A fixed-point-free involution of `Fin 72` has 36 orbits, so its contracted fixed code has length 36. -/
theorem card_orbits {a : Perm (Fin 72)} (ha : orderOf a = 2) (hfp : ∀ i, a i ≠ i) :
    Fintype.card (Orbits a) = 36 := by
  have h := two_mul_card_orbits (mul_self_eq_one_of_orderOf_two ha) hfp
  rw [Fintype.card_fin] at h
  omega

/-- **Theorem D** for `Y_k`, from `H_D k`. -/
theorem thmD_of_HD (k : Fin 41) (hD : H_D k) : ThmD k := by
  intro C hC a ha hord hfp hequiv
  obtain ⟨ψ, hψ⟩ := hequiv
  have ha2 := mul_self_eq_one_of_orderOf_two hord
  have hY : Yof (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) = Yc k := by
    rw [Yof_map_pairEquiv]
    exact hψ
  have hT : TypeII (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) := TypeII.map_reindex hC.1 _
  have hM : MinWt (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) 16 := MinWt.map_reindex hC.2.1 _
  have hinv : ∀ c ∈ C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap,
      permute aStd c ∈ C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap := by
    rintro _ ⟨c, hc, rfl⟩
    show permute aStd (reindex (pairEquiv ha2 hfp ψ) c) ∈ _
    rw [permute_aStd_reindex]
    exact Submodule.mem_map_of_mem (permute_mem_of_mem_Aut ha hc)
  obtain ⟨B, hCB, hsym, hdiag⟩ := model hY hT hinv (Yc_selfDual k)
  obtain ⟨y, hwy, e, he, hcard, hsyn⟩ := hD B ⟨hsym, hdiag⟩
  obtain ⟨c, hcmem, hcwt, hcne⟩ := lemma36 (Yc_selfDual k) B y e he hsyn
  rw [hCB] at hcmem
  have hy0 : (y : Fin 36 → ZMod 2) ≠ 0 := by
    intro h0
    rw [h0, wt, hammingNorm_zero] at hwy
    omega
  have h16 := hM c hcmem (hcne hy0)
  omega

/-- No extremal code has a fixed-point-free involution: T1's `NoFPFInv`, from `H_L2`, `H_L3` and every `H_D k`. -/
theorem noFPFInv_of (hL2 : H_L2) (hL3 : H_L3) (hD : ∀ k, H_D k) : NoFPFInv := by
  intro C hC a ha hord hfp
  obtain ⟨hsd, hmw⟩ := hL2 C hC a ha hord hfp
  let e0 : Orbits a ≃ Fin 36 := Fintype.equivFinOfCardEq (card_orbits hord hfp)
  obtain ⟨k, π, hπ⟩ := hL3 ((contracted a C).map (reindex e0).toLinearMap) (SelfDual.map_reindex hsd e0)
    (MinWtEq.map_reindex hmw e0)
  refine thmD_of_HD k (hD k) C hC a ha hord hfp ⟨e0.trans π, ?_⟩
  rw [← map_reindex_trans]
  exact hπ

/-- No extremal code has an automorphism of order 2: T1's `NoInv`. -/
theorem noInv_of_T4 (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) (hD : ∀ k, H_D k) : NoInv :=
  noInv_of hL1 (noFPFInv_of hL2 hL3 hD)

/-- T1's final deduction with `NoInv` replaced by its T4 sources. -/
theorem main_of_T4 (h1 : H_primes) (hA : ThmA) (hB : ThmB) (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3)
    (hD : ∀ k, H_D k) : ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  main_of_parts h1 hA hB (noInv_of_T4 hL1 hL2 hL3 hD)

end C72.T4
