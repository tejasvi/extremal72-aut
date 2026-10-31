import C72T3.Coords
import Mathlib.FieldTheory.Finiteness

/-!
# T3: the decomposition `C = F ⊕ E` for `g5`, the codes `C₀` and `C₁` (Sec. 2.1)

For a binary code `C` of length 72 with `g5 ∈ Aut C`:

* `C0 C = {u | φ₀u ∈ C} ≤ 𝔽₂¹⁶` and `F = φ₀(C₀)` (`Fsub_eq_map_C0`); `C₀` is self-dual when `C` is
  (`selfDual_C0`, the argument of [Huf82] as in `C72T1.Decomp.contracted_selfDual`).
* Every word of `E` is `φ₁c` (`exists_phi1_of_mem_Esub`).
* `C1 C hg = {c ∈ 𝔽₁₆¹⁴ | φ₁c ∈ C}` is `𝔽₁₆`-linear (a `Submodule F16`), because `g5` acts as
  multiplication by `t` and `t` generates `𝔽₁₆` over `𝔽₂`.
* `C₁` is Hermitian self-orthogonal (`herm_eq_zero`) and Hermitian self-dual (`C1_hSelfDual`) when `C` is
  self-dual [FN12, Lemmas 2.2 and 2.5].
* For an extremal `C`: `dim C₀ = 8`, `dim F = 8`, `dim E = 28` and `|C₁| ≥ 2²⁸` (`card_C1_ge`).
-/

namespace C72.T3

open Equiv Equiv.Perm Finset Module

variable {C : Code 72}

theorem orderOf_g5_prime : (orderOf g5).Prime := by
  rw [orderOf_g5]
  norm_num

theorem orderOf_g5_odd : Odd (orderOf g5) := by
  rw [orderOf_g5]
  decide

/-! ## `C₀` and `F` -/

/-- The contracted fixed code `C₀ = {u | φ₀u ∈ C} ≤ 𝔽₂¹⁶` (Sec. 2.1). -/
def C0 (C : Code 72) : Code 16 :=
  C.comap phi0

theorem mem_C0 {u : Fin 16 → ZMod 2} : u ∈ C0 C ↔ phi0 u ∈ C :=
  Iff.rfl

/-- `F = φ₀(C₀)`. -/
theorem Fsub_eq_map_C0 (C : Code 72) : Fsub C g5 = (C0 C).map phi0 := by
  ext v
  rw [mem_Fsub_iff, Submodule.mem_map]
  constructor
  · rintro ⟨hv, hfix⟩
    obtain ⟨u, rfl⟩ := exists_phi0_eq hfix
    exact ⟨u, hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, phi0_fixed u⟩

/-- `C₀` is self-dual when `C` is [Huf82]. -/
theorem selfDual_C0 (hC : SelfDual C) (hg : g5 ∈ Aut C) : SelfDual (C0 C) := by
  unfold SelfDual
  apply le_antisymm
  · intro u hu
    rw [mem_dual]
    intro u' hu'
    rw [← phi0_dot]
    have h1 : phi0 u ∈ dual C := by
      rw [← hC]
      exact hu
    exact (mem_dual.1 h1) _ hu'
  · intro u hu
    rw [mem_C0, hC, mem_dual]
    intro c hc
    have hsplit : e0 g5 c + (c + e0 g5 c) = c := by
      rw [← add_assoc, add_comm (e0 g5 c) c, add_assoc, vec_add_self, add_zero]
    obtain ⟨u'', hu''⟩ := exists_phi0_eq (e0_apply_apply g5 c)
    have hu''C : u'' ∈ C0 C := by
      rw [mem_C0, hu'']
      exact e0_mem g5 hg hc
    have h1 : phi0 u ⬝ᵥ e0 g5 c = 0 := by
      rw [← hu'', phi0_dot]
      exact (mem_dual.1 hu) u'' hu''C
    have h2 : phi0 u ⬝ᵥ (c + e0 g5 c) = 0 := by
      apply dotProduct_eq_zero_of_fixed g5 orderOf_g5_odd (phi0_fixed u)
      rw [map_add, e0_e0 g5 orderOf_g5_odd, vec_add_self]
    rw [← hsplit, dotProduct_add, h1, h2, add_zero]

/-! ## `E` -/

theorem e0_g5_inl (v : Fin 72 → ZMod 2) (a : Fin 14) :
    e0 g5 v (E72 (Sum.inl (a, 0))) = ∑ b, v (E72 (Sum.inl (a, b))) := by
  rw [e0_apply, orderOf_g5, Finset.sum_range]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [g5_pow_E72, stdShift_pow_inl, finRotate_pow_zero_apply]

theorem e0_g5_inr (v : Fin 72 → ZMod 2) (x : Fin 2) :
    e0 g5 v (E72 (Sum.inr x)) = v (E72 (Sum.inr x)) := by
  rw [e0_apply, orderOf_g5]
  have h : ∀ k : ℕ, (g5 ^ k) (E72 (Sum.inr x)) = E72 (Sum.inr x) := fun k => by
    rw [g5_pow_E72, stdShift_pow_inr]
  simp only [h, Finset.sum_const, Finset.card_range]
  exact zmod2_five_smul _

/-- Every word of `E` is `φ₁c` for some `c ∈ 𝔽₁₆¹⁴`. -/
theorem exists_phi1_of_mem_Esub {v : Fin 72 → ZMod 2} (hv : v ∈ Esub C g5) : ∃ c, phi1 c = v := by
  have he := ((mem_Esub_iff orderOf_g5_prime orderOf_g5_odd).1 hv).2
  refine ⟨fun a => psiInv (fun b => v (E72 (Sum.inl (a, b)))), ?_⟩
  funext i
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [phi1_E72]
  rcases z with ⟨a, b⟩ | x
  · show psi (psiInv (fun b => v (E72 (Sum.inl (a, b))))) b = v (E72 (Sum.inl (a, b)))
    have hsum : ∑ b, v (E72 (Sum.inl (a, b))) = 0 := by
      have h := congrFun he (E72 (Sum.inl (a, 0)))
      rwa [e0_g5_inl] at h
    rw [psi_psiInv _ hsum]
  · show 0 = v (E72 (Sum.inr x))
    have h := congrFun he (E72 (Sum.inr x))
    rw [e0_g5_inr] at h
    exact h.symm

/-! ## `C₁` -/

theorem t_smul_mem (hg : g5 ∈ Aut C) {c : Fin 14 → F16} (hc : phi1 c ∈ C) : phi1 (F16.t • c) ∈ C := by
  rw [← permute_g5_phi1]
  exact permute_mem_of_mem_Aut hg hc

theorem coeff_zero_or_one (y : F16) (k : ℕ) : F16.coeff y k = 0 ∨ F16.coeff y k = 1 := by
  unfold F16.coeff
  cases y.val.val.testBit k
  · left
    rfl
  · right
    rfl

theorem coeff_smul_mem {y : F16} (k : ℕ) {w : Fin 14 → F16} (hw : phi1 w ∈ C) :
    phi1 (F16.coeff y k • w) ∈ C := by
  rcases coeff_zero_or_one y k with h | h
  · rw [h, zero_smul, map_zero]
    exact C.zero_mem
  · rw [h, one_smul]
    exact hw

/-- `C₁` is closed under multiplication by every element of `𝔽₁₆`: `y = Σ_k y_k t^k`. -/
theorem smul_mem_C1 (hg : g5 ∈ Aut C) (y : F16) {c : Fin 14 → F16} (hc : phi1 c ∈ C) :
    phi1 (y • c) ∈ C := by
  have ht1 := t_smul_mem hg hc
  have ht2 := t_smul_mem hg ht1
  have ht3 := t_smul_mem hg ht2
  have e : y • c = F16.coeff y 0 • c + F16.coeff y 1 • (F16.t • c) +
      F16.coeff y 2 • (F16.t • F16.t • c) + F16.coeff y 3 • (F16.t • F16.t • F16.t • c) := by
    conv_lhs => rw [F16.eq_poly y]
    simp only [add_smul, mul_smul, pow_succ, pow_zero, one_mul]
  rw [e, map_add, map_add, map_add]
  exact C.add_mem (C.add_mem (C.add_mem (coeff_smul_mem 0 hc) (coeff_smul_mem 1 ht1))
    (coeff_smul_mem 2 ht2)) (coeff_smul_mem 3 ht3)

/-- `C₁ = {c ∈ 𝔽₁₆¹⁴ | φ₁c ∈ C}` (Sec. 2.1), an `𝔽₁₆`-linear code. -/
def C1 (C : Code 72) (hg : g5 ∈ Aut C) : Submodule F16 (Fin 14 → F16) where
  carrier := {c | phi1 c ∈ C}
  add_mem' := by
    intro c c' hc hc'
    show phi1 (c + c') ∈ C
    rw [map_add]
    exact C.add_mem hc hc'
  zero_mem' := by
    show phi1 0 ∈ C
    rw [map_zero]
    exact C.zero_mem
  smul_mem' := fun y _ hc => smul_mem_C1 hg y hc

theorem mem_C1 {hg : g5 ∈ Aut C} {c : Fin 14 → F16} : c ∈ C1 C hg ↔ phi1 c ∈ C :=
  Iff.rfl

/-- `C₁` is Hermitian self-orthogonal: `⟨c, c'⟩ = 0`, because `Tr(λ⟨c, c'⟩) = ⟨φ₁(λc), φ₁c'⟩ = 0` for all `λ`
and the trace form is nondegenerate. -/
theorem herm_eq_zero (hC : SelfDual C) {hg : g5 ∈ Aut C} {c c' : Fin 14 → F16} (hc : c ∈ C1 C hg)
    (hc' : c' ∈ C1 C hg) : herm c c' = 0 := by
  apply tr_nondeg
  intro l
  have h1 : phi1 (l • c) ∈ C := (C1 C hg).smul_mem l hc
  have h3 : phi1 (l • c) ⬝ᵥ phi1 c' = 0 := by
    have h4 : phi1 (l • c) ∈ dual C := by
      rw [← hC]
      exact h1
    exact (mem_dual.1 h4) _ hc'
  rw [phi1_dot, herm_smul_left] at h3
  exact h3

/-- **`C₁` is `𝔽₁₆`-linear and Hermitian self-dual** [FN12, Lemmas 2.2 and 2.5]. -/
theorem C1_hSelfDual (hC : SelfDual C) (hg : g5 ∈ Aut C) : HSelfDual (C1 C hg) := by
  apply le_antisymm
  · intro c hc
    exact fun c' hc' => herm_eq_zero hC hc hc'
  · intro c hc
    show phi1 c ∈ C
    rw [hC, mem_dual]
    intro x hx
    have hsplit : e0 g5 x + (x + e0 g5 x) = x := by
      rw [← add_assoc, add_comm (e0 g5 x) x, add_assoc, vec_add_self, add_zero]
    obtain ⟨u, hu⟩ := exists_phi0_eq (e0_apply_apply g5 x)
    have hE : x + e0 g5 x ∈ Esub C g5 := by
      rw [mem_Esub_iff orderOf_g5_prime orderOf_g5_odd]
      refine ⟨C.add_mem hx (e0_mem g5 hg hx), ?_⟩
      rw [map_add, e0_e0 g5 orderOf_g5_odd, vec_add_self]
    obtain ⟨c'', hc''⟩ := exists_phi1_of_mem_Esub hE
    have hc''C : c'' ∈ C1 C hg := by
      show phi1 c'' ∈ C
      rw [hc'']
      exact Esub_le C g5 hE
    rw [← hsplit, dotProduct_add, ← hc'', ← hu, phi1_dot_phi0, phi1_dot, (mem_hdual.1 hc) c'' hc''C,
      tr_zero, zero_add]

/-! ## Dimensions -/

theorem finrank_C0 (hC : SelfDual C) (hg : g5 ∈ Aut C) : finrank (ZMod 2) (C0 C) = 8 := by
  have h := SelfDual.two_mul_finrank (K := ZMod 2) (selfDual_C0 hC hg)
  simp only [Fintype.card_fin] at h
  omega

theorem finrank_Fsub (hC : SelfDual C) (hg : g5 ∈ Aut C) : finrank (ZMod 2) (Fsub C g5) = 8 := by
  rw [Fsub_eq_map_C0, ← (Submodule.equivMapOfInjective phi0 phi0_injective (C0 C)).finrank_eq]
  exact finrank_C0 hC hg

/-- For an extremal code, `dim E = 36 − 8 = 28`. -/
theorem finrank_Esub (hC : Ext72 C) (hg : g5 ∈ Aut C) : finrank (ZMod 2) (Esub C g5) = 28 := by
  obtain ⟨hsup, hinf, -⟩ := decomposition (by norm_num : Nat.Prime 5) (by norm_num) orderOf_g5 hg
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Fsub C g5) (Esub C g5)
  rw [hsup, hinf, finrank_bot, Ext72.finrank hC, finrank_Fsub hC.1.1 hg] at h
  omega

theorem card_Esub (hC : Ext72 C) (hg : g5 ∈ Aut C) : Nat.card (Esub C g5) = 2 ^ 28 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_Esub hC hg, Nat.card_zmod]

/-- `|C₁| ≥ |E| = 2²⁸`: `φ₁` maps `C₁` onto `E`. -/
theorem card_C1_ge (hC : Ext72 C) (hg : g5 ∈ Aut C) : 2 ^ 28 ≤ Nat.card (C1 C hg) := by
  rw [← card_Esub hC hg]
  have hex : ∀ v : Esub C g5, ∃ c : Fin 14 → F16, phi1 c = v := fun v => exists_phi1_of_mem_Esub v.2
  choose f hf using hex
  refine Nat.card_le_card_of_injective (fun v => ⟨f v, ?_⟩) ?_
  · show phi1 (f v) ∈ C
    rw [hf v]
    exact Esub_le C g5 v.2
  · intro v w hvw
    apply Subtype.ext
    have h : f v = f w := congrArg Subtype.val hvw
    rw [← hf v, ← hf w, h]

end C72.T3
