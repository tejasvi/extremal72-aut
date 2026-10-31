import C72T6K.Klein

/-!
# T6: Proposition 3.7, the instances of the Klein case

A subgroup `C₂ × C₂` of `Aut C` is given by two distinct commuting involutions `a`, `b` (`KleinPair`;
`kleinPair_of_mulEquiv` derives them from a subgroup isomorphic to `C₂ × C₂`).

* **Forward** (`prop37_forward`): if (L1), (L2), (L3) hold (T1's `H_L1`, T4's `H_L2`, `H_L3`), an extremal code `C` with a
  Klein pair is equivalent to `C_B` for some `k`, a fixed-point-free involution `β ∈ Aut(Y_k)` and a form `B ∈ A(Y_k, β)`
  that is not ruled out. The form of the slice of `G` in `B + G` is then a solution of the instance `(Y_k, β)`, for every
  echelon basis of `G` (`prop37_forward_slice`), and `β` may be taken from any set of representatives of the conjugacy
  classes of fixed-point-free involutions in `Aut(Y_k)` (`prop37_forward_reps`). On the pairs: `klein_forward_pairs`.
* **Backward** (`prop37_converse`): a solution of an instance gives a Type II code on `Fin 36 × 𝔽₂` with minimum weight at
  least 16 and the Klein pair `a = aStd`, `b = liftP β` of fixed-point-free involutions (`a b` too), with contracted fixed
  code `Y_k` (the Klein pair: `kleinPair_CB`). The minimum weight 8 of `Y_k` is a premise (not checked in Lean).
* **Proposition 3.8** from the searches (`prop38_of_searches`): if for each representative `β` some slice of `G` (the
  program's) has no solution, no extremal code has a Klein pair. The search claim is a hypothesis of this theorem.

`IsSolK` uses every constraint word and the programs' patterns; for `B ∈ A(Y, β)` this is the paper's condition, with one
word from each orbit `{y, y β}` and the sets `E_{|y|}` (`ruledOut_iff_reps_E`), so the solutions are the paper's
(`isSolK_iff_isSolKE`).
-/

namespace C72.T6

open C72 C72.T4 Module Finset Equiv

/-- `⟨a, b⟩ ≤ Aut C` is a Klein four-group: `a` and `b` are distinct commuting involutions of `Aut C`. -/
def KleinPair {κ : Type*} (C : Submodule (ZMod 2) (κ → ZMod 2)) (a b : Perm κ) : Prop :=
  a ∈ Aut C ∧ b ∈ Aut C ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b

/-- A subgroup of `Aut C` isomorphic to `C₂ × C₂` gives a Klein pair. -/
theorem kleinPair_of_mulEquiv {κ : Type*} {C : Submodule (ZMod 2) (κ → ZMod 2)} (V : Subgroup (Perm κ))
    (hV : V ≤ Aut C) (φ : Multiplicative (ZMod 2 × ZMod 2) ≃* V) :
    KleinPair C (φ (Multiplicative.ofAdd (1, 0))) (φ (Multiplicative.ofAdd (0, 1))) := by
  have h10 : orderOf (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have h01 : orderOf (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  refine ⟨hV (φ _).2, hV (φ _).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h10]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h01]
  · have h := congrArg (fun z => ((φ z : V) : Perm κ))
      (mul_comm (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) (Multiplicative.ofAdd (0, 1)))
    simp only [map_mul, Subgroup.coe_mul] at h
    exact h
  · intro h
    have h' := congrArg Multiplicative.toAdd (φ.injective (Subtype.ext h))
    exact absurd h' (by decide)

theorem aStd_mul_self {ι : Type*} : (aStd : Perm (ι × ZMod 2)) * aStd = 1 := by
  ext ⟨i, e⟩
  · rfl
  · show e + 1 + 1 = e
    rw [add_assoc, zmod2_add_self', add_zero]

theorem permute_permCongr_reindex {κ μ : Type*} (e : κ ≃ μ) (b : Perm κ) (c : κ → ZMod 2) :
    permute (e.permCongr b) (reindex e c) = reindex e (permute b c) := by
  funext x
  rw [permute_apply, reindex_apply, reindex_apply, permute_apply]
  congr 1
  simp only [Equiv.permCongr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- A form whose code has minimum weight at least 16 is not ruled out (T4's `lemma36`). -/
theorem not_ruledOut_of_minWt (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y) (hM : MinWt (CB Y B) 16) :
    ¬ RuledOut Y B := by
  rintro ⟨y, hwy, e, he, hcard, hsyn⟩
  obtain ⟨c, hcmem, hcwt, hcne⟩ := lemma36 hY B y e he hsyn
  unfold IsConstraint at hwy
  have hy0 : (y : ι → ZMod 2) ≠ 0 := by
    intro h0
    rw [h0, wt, hammingNorm_zero] at hwy
    omega
  have h16 := hM c hcmem (hcne hy0)
  omega

/-- **Proposition 3.7, forward, on the pairs.** A Type II code `C` on `ι × 𝔽₂` with the automorphism `a = aStd`, contracted
fixed code `Y`, and an involution `b ∈ Aut C` that commutes with `a`, with `b` and `a b` fixed-point-free, is moved by a
swap of pairs `s` (which commutes with `a`) onto `C_B` for a form `B ∈ A(Y, β)`, where `β ∈ Aut Y` is a fixed-point-free
involution (Lemmas 3.2, 3.3 and 3.4). -/
theorem klein_forward_pairs [LinearOrder ι] (hY : SelfDual Y) (h1 : allOnes ∈ Y)
    {C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)} (hC : TypeII C) (ha : ∀ c ∈ C, permute aStd c ∈ C)
    (hYC : Yof C = Y) {b : Perm (ι × ZMod 2)} (hb : b ∈ Aut C) (hab : b * aStd = aStd * b) (hb2 : b * b = 1)
    (hbfp : ∀ p, b p ≠ p) (habfp : ∀ p, ((aStd : Perm (ι × ZMod 2)) * b) p ≠ p) :
    ∃ β : Aut Y, IsFPFInv (β : Perm ι) ∧ ∃ B, InA Y h1 β B ∧ ∃ s : Perm (ι × ZMod 2),
      s * aStd = aStd * s ∧ C.map (permute s).toLinearMap = CB Y B := by
  obtain ⟨β, t, hbt⟩ := pair_form b hab
  obtain ⟨hβ2, ht⟩ := pair_form_props hbt hb2
  have hβfp := pair_form_fpf hbt hbfp habfp
  have hβY : β ∈ Aut Y := hYC ▸ mem_Aut_Yof_of_pair_form hb hbt
  obtain ⟨J, hJ⟩ := exists_swapP hβ2 hβfp ht
  have hconj := swapP_conj hbt hJ
  have hss := swapP_mul_self J
  have hT' : TypeII (C.map (permute (swapP J)).toLinearMap) := hC.map_permute _
  have ha' : ∀ c ∈ C.map (permute (swapP J)).toLinearMap,
      permute aStd c ∈ C.map (permute (swapP J)).toLinearMap := by
    rintro _ ⟨c, hc, rfl⟩
    show permute aStd (permute (swapP J) c) ∈ _
    rw [← permute_mul, ← swapP_mul_aStd, permute_mul]
    exact Submodule.mem_map_of_mem (ha c hc)
  have hY' : Yof (C.map (permute (swapP J)).toLinearMap) = Y := by
    rw [← hYC]
    ext u
    rw [mem_Yof, mem_Yof]
    constructor
    · rintro ⟨c, hc, hcu⟩
      have h : permute (swapP J) (permute (swapP J) c) = permute (swapP J) (pv u u) :=
        congrArg (fun x => permute (swapP J) x) hcu
      rw [permute_swapP_pv_self, ← permute_mul, hss, permute_one_apply] at h
      rw [← h]
      exact hc
    · intro hu
      exact ⟨pv u u, hu, permute_swapP_pv_self J u⟩
  obtain ⟨B, hCB, hsym, hdiag⟩ := model hY' hT' ha' hY
  have hlift : liftP β ∈ Aut (C.map (permute (swapP J)).toLinearMap) := by
    rw [mem_Aut_iff]
    rintro _ ⟨c, hc, rfl⟩
    show permute (liftP β) (permute (swapP J) c) ∈ _
    rw [← permute_mul, ← hconj, mul_assoc, hss, mul_one, permute_mul]
    exact Submodule.mem_map_of_mem (permute_mem_of_mem_Aut hb hc)
  refine ⟨⟨β, hβY⟩, ⟨hβ2, hβfp⟩, B, ⟨⟨hsym, hdiag⟩, ?_⟩, swapP J, swapP_mul_aStd J, hCB.symm⟩
  rw [← liftP_mem_Aut_CB_iff, hCB]
  exact hlift

/-- The solutions of the instance `(Y_k, β)` in the slice of an echelon basis of `G`: forms of `A(Y_k, β)` in the slice
that are not ruled out. -/
def IsSolK (k : Fin 41) (β : Aut (Yc k)) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m)
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : Prop :=
  InA (Yc k) (allOnes_mem_Yc k) β B ∧ B ∈ slice E ∧ ¬ RuledOut (Yc k) B

/-- A form of `A(Y_k, β)` that is not ruled out gives a solution in every slice of `G` (Lemma 3.5 (c) for forms). -/
theorem exists_isSolK (k : Fin 41) (β : Aut (Yc k)) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m) {B : LinearMap.BilinForm (ZMod 2) (Yc k)}
    (hB : InA (Yc k) (allOnes_mem_Yc k) β B) (hnr : ¬ RuledOut (Yc k) B) : ∃ B', IsSolK k β E B' := by
  have hD := sliceRep_sub_mem E B
  have hrep : B + (sliceRep E B - B) = sliceRep E B := by abel
  refine ⟨sliceRep E B, ?_, sliceRep_mem_slice E B, ?_⟩
  · rw [← hrep]
    exact InA_add (Yc_selfDual k) hB hD
  · rw [← hrep, ruledOut_add_iff _ (GK_le_G0 β hD)]
    exact hnr

/-- For `B ∈ A(Y, β)` the programs' condition (every constraint word, the larger pattern sets) is the paper's condition
(one word from each orbit `{y, y β}`, `Bad(y)` with the sets `E_{|y|}`), for every set `R` that contains `y` or `y β` for
each constraint word `y`. -/
theorem ruledOut_iff_reps_E (hY : SelfDual Y) {h1 : allOnes ∈ Y} (β : Aut Y) (hβ2 : (β : Perm ι) * β = 1)
    {B : LinearMap.BilinForm (ZMod 2) Y} (hB : InA Y h1 β B) (R : Set Y)
    (hR : ∀ y : Y, IsConstraint (y : ι → ZMod 2) → y ∈ R ∨ autLin β y ∈ R) :
    RuledOut Y B ↔ ∃ y ∈ R, IsConstraint (y : ι → ZMod 2) ∧ BadAtE Y B y := by
  rw [ruledOut_iff_reps β hβ2 hB.2 R hR]
  constructor
  · rintro ⟨y, hyR, hy, hbad⟩
    exact ⟨y, hyR, hy, badAtE_of_badAt hY hB.1 hy hbad⟩
  · rintro ⟨y, hyR, hy, hbad⟩
    exact ⟨y, hyR, hy, badAt_of_badAtE hy hbad⟩

/-- The paper's solutions of the instance `(Y_k, β)` (Section 3.5): forms of the slice `S(Y_k, β)` with `s_y(B) ∉ Bad(y)`
for the constraint words `y ∈ R`. -/
def IsSolKE (k : Fin 41) (β : Aut (Yc k)) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m) (R : Set (Yc k))
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : Prop :=
  InA (Yc k) (allOnes_mem_Yc k) β B ∧ B ∈ slice E ∧ ¬ ∃ y ∈ R, IsConstraint (y : Fin 36 → ZMod 2) ∧ BadAtE (Yc k) B y

/-- The solutions of `IsSolK` are the paper's, for every set `R` of constraint words with one word from each orbit. -/
theorem isSolK_iff_isSolKE (k : Fin 41) (β : Aut (Yc k)) (hβ2 : (β : Perm (Fin 36)) * β = 1) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m) (R : Set (Yc k))
    (hR : ∀ y : Yc k, IsConstraint (y : Fin 36 → ZMod 2) → y ∈ R ∨ autLin β y ∈ R)
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : IsSolK k β E B ↔ IsSolKE k β E R B := by
  constructor
  · rintro ⟨hA, hs, hnr⟩
    exact ⟨hA, hs, fun h => hnr ((ruledOut_iff_reps_E (Yc_selfDual k) β hβ2 hA R hR).2 h)⟩
  · rintro ⟨hA, hs, hnr⟩
    exact ⟨hA, hs, fun h => hnr ((ruledOut_iff_reps_E (Yc_selfDual k) β hβ2 hA R hR).1 h)⟩

/-- **Proposition 3.7, forward.** Under (L1), (L2), (L3), an extremal code with a Klein pair is equivalent to `C_B` for a
form `B ∈ A(Y_k, β)` that is not ruled out, `β ∈ Aut(Y_k)` a fixed-point-free involution. -/
theorem prop37_forward (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) {C : Code 72} (hC : Ext72 C) {a b : Perm (Fin 72)}
    (hK : KleinPair C a b) :
    ∃ k : Fin 41, ∃ β : Aut (Yc k), IsFPFInv (β : Perm (Fin 36)) ∧
      ∃ B, InA (Yc k) (allOnes_mem_Yc k) β B ∧ ¬ RuledOut (Yc k) B ∧ CodeEquiv C (CB (Yc k) B) := by
  obtain ⟨ha, hb, hoa, hob, hcomm, hne⟩ := hK
  have hfa := hL1 C hC a ha hoa
  have hfb := hL1 C hC b hb hob
  have ha2 := mul_self_eq_one_of_orderOf_two hoa
  have hb2 := mul_self_eq_one_of_orderOf_two hob
  have hoab : orderOf (a * b) = 2 := by
    have ha2' : a ^ 2 = 1 := hoa ▸ pow_orderOf_eq_one a
    have hb2' : b ^ 2 = 1 := hob ▸ pow_orderOf_eq_one b
    apply orderOf_eq_prime
    · rw [Commute.mul_pow hcomm, ha2', hb2', one_mul]
    · intro h1
      apply hne
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right ha2]
  have hfab := hL1 C hC (a * b) ((Aut C).mul_mem ha hb) hoab
  obtain ⟨hsd, hmw⟩ := hL2 C hC a ha hoa hfa
  let e0 : Orbits a ≃ Fin 36 := Fintype.equivFinOfCardEq (card_orbits hoa hfa)
  obtain ⟨k, π, hπ⟩ := hL3 ((contracted a C).map (reindex e0).toLinearMap) (SelfDual.map_reindex hsd e0)
    (MinWtEq.map_reindex hmw e0)
  have hψ : (contracted a C).map (reindex (e0.trans π)).toLinearMap = Yc k := by
    rw [← map_reindex_trans]
    exact hπ
  have hY : Yof (C.map (reindex (pairEquiv ha2 hfa (e0.trans π))).toLinearMap) = Yc k := by
    rw [Yof_map_pairEquiv]
    exact hψ
  set e := pairEquiv ha2 hfa (e0.trans π) with he
  have hT : TypeII (C.map (reindex e).toLinearMap) := TypeII.map_reindex hC.1 e
  have hM : MinWt (C.map (reindex e).toLinearMap) 16 := MinWt.map_reindex hC.2.1 e
  have hinv : ∀ c ∈ C.map (reindex e).toLinearMap, permute aStd c ∈ C.map (reindex e).toLinearMap := by
    rintro _ ⟨c, hc, rfl⟩
    show permute aStd (reindex e c) ∈ _
    rw [he, permute_aStd_reindex]
    exact Submodule.mem_map_of_mem (permute_mem_of_mem_Aut ha hc)
  have hea : ∀ j, e (a j) = aStd (e j) := pairEquiv_apply_apply ha2 hfa (e0.trans π)
  have hb'C : e.permCongr b ∈ Aut (C.map (reindex e).toLinearMap) := by
    rw [mem_Aut_iff]
    rintro _ ⟨c, hc, rfl⟩
    show permute (e.permCongr b) (reindex e c) ∈ _
    rw [permute_permCongr_reindex]
    exact Submodule.mem_map_of_mem (permute_mem_of_mem_Aut hb hc)
  have hb'a : e.permCongr b * aStd = aStd * e.permCongr b := by
    ext1 x
    obtain ⟨j, rfl⟩ := e.surjective x
    show e (b (e.symm (aStd (e j)))) = aStd (e (b (e.symm (e j))))
    rw [← hea, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hea]
    exact congrArg e (congrArg (fun f : Perm (Fin 72) => f j) hcomm).symm
  have hb'2 : e.permCongr b * e.permCongr b = 1 := by
    ext1 x
    show e (b (e.symm (e (b (e.symm x))))) = x
    rw [Equiv.symm_apply_apply]
    have h := congrArg (fun f : Perm (Fin 72) => f (e.symm x)) hb2
    simp only [Perm.mul_apply, Perm.one_apply] at h
    rw [h, Equiv.apply_symm_apply]
  have hb'fp : ∀ p, e.permCongr b p ≠ p := by
    intro p hp
    obtain ⟨j, rfl⟩ := e.surjective p
    apply hfb j
    apply e.injective
    rw [← hp]
    show e (b j) = e (b (e.symm (e j)))
    rw [Equiv.symm_apply_apply]
  have hab'fp : ∀ p, ((aStd : Perm (Fin 36 × ZMod 2)) * e.permCongr b) p ≠ p := by
    intro p hp
    obtain ⟨j, rfl⟩ := e.surjective p
    apply hfab j
    apply e.injective
    rw [← hp]
    show e (a (b j)) = aStd (e (b (e.symm (e j))))
    rw [Equiv.symm_apply_apply, hea]
  obtain ⟨β, hβ, B, hB, s, -, hs⟩ :=
    klein_forward_pairs (Yc_selfDual k) (allOnes_mem_Yc k) hT hinv hY hb'C hb'a hb'2 hb'fp hab'fp
  refine ⟨k, β, hβ, B, hB, not_ruledOut_of_minWt (Yc_selfDual k) B ?_, e.trans s, ?_⟩
  · rw [← hs]
    exact MinWt.map_permute hM s
  · rw [← map_reindex_trans, reindex_perm]
    exact hs

/-- **Proposition 3.7, forward, on the slices.** In the situation of `prop37_forward`, the instance `(Y_k, β)` has a
solution in every slice of `G`. -/
theorem prop37_forward_slice (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) {C : Code 72} (hC : Ext72 C)
    {a b : Perm (Fin 72)} (hK : KleinPair C a b) :
    ∃ k : Fin 41, ∃ β : Aut (Yc k), IsFPFInv (β : Perm (Fin 36)) ∧
      ∀ (m : ℕ) (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m), ∃ B, IsSolK k β E B := by
  obtain ⟨k, β, hβ, B, hB, hnr, -⟩ := prop37_forward hL1 hL2 hL3 hC hK
  exact ⟨k, β, hβ, fun m E => exists_isSolK k β E hB hnr⟩

/-- **Proposition 3.7, forward, with representatives.** For any sets `R k` of representatives of the conjugacy classes
of fixed-point-free involutions in `Aut(Y_k)`, some instance `(Y_k, β)` with `β ∈ R k` has a solution in every slice. -/
theorem prop37_forward_reps (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) (R : ∀ k : Fin 41, Set (Aut (Yc k)))
    (hR : ∀ (k : Fin 41) (β : Aut (Yc k)), IsFPFInv (β : Perm (Fin 36)) → ∃ g : Aut (Yc k), g⁻¹ * β * g ∈ R k)
    {C : Code 72} (hC : Ext72 C) {a b : Perm (Fin 72)} (hK : KleinPair C a b) :
    ∃ k : Fin 41, ∃ β ∈ R k, IsFPFInv (β : Perm (Fin 36)) ∧
      ∀ (m : ℕ) (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m), ∃ B, IsSolK k β E B := by
  obtain ⟨k, β, hβ, B, hB, hnr, -⟩ := prop37_forward hL1 hL2 hL3 hC hK
  obtain ⟨g, hg⟩ := hR k β hβ
  obtain ⟨hB', hro⟩ := InA_conj hB g
  exact ⟨k, g⁻¹ * β * g, hg, isFPFInv_conj hβ g, fun m E => exists_isSolK k _ E hB' (fun h => hnr (hro h))⟩

omit [DecidableEq ι] in
/-- **Lemma 3.4 (c) and the end of the proof of Proposition 3.7.** For a fixed-point-free involution `β ∈ Aut Y` and a
`β`-invariant form `B`, the involutions `a = aStd` and `b = liftP β` form a Klein pair in `Aut(C_B)`, and `a`, `b` and
`a b` are fixed-point-free ("they generate a group `C₂ × C₂`, since `b` moves the pairs"). -/
theorem kleinPair_CB [Nonempty ι] (hY : SelfDual Y) (β : Aut Y) (hβ : IsFPFInv (β : Perm ι))
    (B : LinearMap.BilinForm (ZMod 2) Y) (hB : formAct β B = B) :
    KleinPair (CB Y B) aStd (liftP (β : Perm ι)) ∧ (∀ p : ι × ZMod 2, aStd p ≠ p) ∧
      (∀ p, liftP (β : Perm ι) p ≠ p) ∧ ∀ p, ((aStd : Perm (ι × ZMod 2)) * liftP (β : Perm ι)) p ≠ p := by
  have key : ∀ x : ZMod 2, x + 1 ≠ x := by decide
  obtain ⟨i0⟩ := ‹Nonempty ι›
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact mem_Aut_iff.2 (aStd_mem_CB hY B)
  · exact (liftP_mem_Aut_CB_iff β B).2 hB
  · apply orderOf_eq_prime
    · rw [sq, aStd_mul_self]
    · intro h
      have h' : (aStd ((i0, 0) : ι × ZMod 2)).2 = ((1 : Perm (ι × ZMod 2)) (i0, 0)).2 :=
        congrArg (fun f : Perm (ι × ZMod 2) => (f (i0, 0)).2) h
      change (0 : ZMod 2) + 1 = 0 at h'
      exact key 0 h'
  · apply orderOf_eq_prime
    · rw [sq, ← liftP_mul, hβ.1]
      ext ⟨i, e⟩ <;> rfl
    · intro h
      have h' : (liftP (β : Perm ι) (i0, 0)).1 = ((1 : Perm (ι × ZMod 2)) (i0, 0)).1 :=
        congrArg (fun f : Perm (ι × ZMod 2) => (f (i0, 0)).1) h
      exact hβ.2 i0 h'
  · exact (liftP_mul_aStd (β : Perm ι)).symm
  · intro h
    have h' : (aStd ((i0, 0) : ι × ZMod 2)).2 = (liftP (β : Perm ι) (i0, 0)).2 :=
      congrArg (fun f : Perm (ι × ZMod 2) => (f (i0, 0)).2) h
    change (0 : ZMod 2) + 1 = 0 at h'
    exact key 0 h'
  · intro p hp
    exact key p.2 (congrArg Prod.snd hp)
  · intro p hp
    exact hβ.2 p.1 (congrArg Prod.fst hp)
  · intro p hp
    exact key p.2 (congrArg Prod.snd hp)

/-- **Proposition 3.7, backward (pairs).** A form of `A(Y_k, β)` that is not ruled out (for instance a solution of the
instance `(Y_k, β)`) gives a Type II code on `Fin 36 × 𝔽₂` with minimum weight at least 16, contracted fixed code `Y_k`,
and the Klein pair `aStd`, `liftP β` of fixed-point-free involutions whose product is fixed-point-free too. -/
theorem prop37_converse (k : Fin 41) (β : Aut (Yc k)) (hβ : IsFPFInv (β : Perm (Fin 36)))
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) (hB : InA (Yc k) (allOnes_mem_Yc k) β B) (hnr : ¬ RuledOut (Yc k) B)
    (h8 : MinWt (Yc k) 8) :
    TypeII (CB (Yc k) B) ∧ MinWt (CB (Yc k) B) 16 ∧ Yof (CB (Yc k) B) = Yc k ∧
      KleinPair (CB (Yc k) B) aStd (liftP (β : Perm (Fin 36))) ∧ (∀ p : Fin 36 × ZMod 2, aStd p ≠ p) ∧
      (∀ p, liftP (β : Perm (Fin 36)) p ≠ p) ∧
      ∀ p, ((aStd : Perm (Fin 36 × ZMod 2)) * liftP (β : Perm (Fin 36))) p ≠ p :=
  ⟨⟨CB_selfDual (Yc_selfDual k) B hB.1.1, CB_doublyEven (Yc_selfDual k) (allOnes_mem_Yc k) B hB.1.2⟩,
    minWt_CB (Yc_selfDual k) h8 (allOnes_mem_Yc k) B hB.1 hnr, Yof_CB (Yc_selfDual k) B,
    kleinPair_CB (Yc_selfDual k) β hβ B hB.2⟩

/-- **Proposition 3.8 from the searches.** Under (L1), (L2), (L3): if, for each `k` and each representative `β ∈ R k`, some
slice of `G` (the program's) contains no solution of the instance `(Y_k, β)`, then no extremal code has a Klein pair
("by Proposition 3.7 it suffices that no instance has a solution"). -/
theorem prop38_of_searches (hL1 : H_L1) (hL2 : H_L2) (hL3 : H_L3) (R : ∀ k : Fin 41, Set (Aut (Yc k)))
    (hR : ∀ (k : Fin 41) (β : Aut (Yc k)), IsFPFInv (β : Perm (Fin 36)) → ∃ g : Aut (Yc k), g⁻¹ * β * g ∈ R k)
    (hsearch : ∀ k : Fin 41, ∀ β ∈ R k, ∃ m : ℕ,
      ∃ E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (GK β) m, ∀ B, ¬ IsSolK k β E B) :
    ∀ C : Code 72, Ext72 C → ∀ a b : Perm (Fin 72), ¬ KleinPair C a b := by
  intro C hC a b hK
  obtain ⟨k, β, hβR, -, hsol⟩ := prop37_forward_reps hL1 hL2 hL3 R hR hC hK
  obtain ⟨m, E, hE⟩ := hsearch k β hβR
  obtain ⟨B, hB⟩ := hsol m E
  exact hE B hB

end C72.T6
