import C72T3.Lemma22
import C72T3.L23
import C72T1.Final

/-!
# T3: the reduction to a unitary matrix and Theorem A (Sec. 2.3)

In the layout of Sec. 2.2 (`C₀ = e8e8w`), for an extremal code `C` with `g5 ∈ Aut C`:

* a word of `C₁` with `c_B = 0` (or `c_A = 0`) is zero: otherwise every `λc` is a nonzero word of `C₁`, so
  Lemma 2.2 gives `M(λ c_A) ≥ 16` for all `λ ≠ 0`, while `⟨c_A, c_A⟩ = ⟨c, c⟩ = 0`, against Lemma 2.3
  (`eq_zero_of_cB_eq_zero`, `eq_zero_of_cA_eq_zero`);
* so the projection `c ↦ c_A` is injective on `C₁`, and bijective because `|C₁| ≥ 2²⁸ = |𝔽₁₆⁷|`;
* `U` has as row `i` the `B`-half of the word of `C₁` whose `A`-half is the unit vector `e_i`. Then
  `(a, aU) ∈ C₁` for all `a` (`F16`-linearity), and `UU* = I` because `C₁` is Hermitian self-orthogonal;
* `H_A` gives a nonzero `a` with `M(a) + M(aU) < 16`, against Lemma 2.2 (`core`).

**Theorem A** (`C72.thmA_of_hyps`): from `H_CP5`, `H_16` and `H_A`, no doubly-even self-dual `[72,36,16]` code
has an automorphism of order 5. `ThmA` is the statement of `C72T1.Final`.
-/

namespace C72.T3

open Equiv Equiv.Perm Finset Matrix

variable {C : Code 72}

theorem herm_split (c c' : Fin 14 → F16) : herm c c' = herm (cA c) (cA c') + herm (cB c) (cB c') := by
  rw [herm, sum_fin14]
  rfl

theorem cA_smul (l : F16) (c : Fin 14 → F16) : cA (l • c) = l • cA c :=
  rfl

theorem cB_smul (l : F16) (c : Fin 14 → F16) : cB (l • c) = l • cB c :=
  rfl

theorem cA_sub (c c' : Fin 14 → F16) : cA (c - c') = cA c - cA c' :=
  rfl

theorem cA_zero : cA 0 = 0 :=
  rfl

theorem cB_zero : cB 0 = 0 :=
  rfl

/-- In `C₁`, a word with `c_B = 0` is zero. -/
theorem eq_zero_of_cB_eq_zero (hC : Ext72 C) (hC0 : C0 C = e8e8w) {hg : g5 ∈ Aut C} {c : Fin 14 → F16}
    (hc : c ∈ C1 C hg) (hB : cB c = 0) : c = 0 := by
  by_contra hne
  have hA : cA c ≠ 0 := fun hA => hne (cA_ext (hA.trans cA_zero.symm) (hB.trans cB_zero.symm))
  have hiso : herm (cA c) (cA c) = 0 := by
    have h := herm_eq_zero hC.1.1 hc hc
    rw [herm_split, hB, herm_zero_left, add_zero] at h
    exact h
  obtain ⟨l, hl, hM⟩ := lemma23 (cA c) hA hiso
  have h16 := lemma22 hC.2.1 hC0 ((C1 C hg).smul_mem l hc) (smul_ne_zero hl hne)
  rw [cA_smul, cB_smul, hB, smul_zero, M_zero, add_zero] at h16
  omega

/-- In `C₁`, a word with `c_A = 0` is zero. -/
theorem eq_zero_of_cA_eq_zero (hC : Ext72 C) (hC0 : C0 C = e8e8w) {hg : g5 ∈ Aut C} {c : Fin 14 → F16}
    (hc : c ∈ C1 C hg) (hA : cA c = 0) : c = 0 := by
  by_contra hne
  have hB : cB c ≠ 0 := fun hB => hne (cA_ext (hA.trans cA_zero.symm) (hB.trans cB_zero.symm))
  have hiso : herm (cB c) (cB c) = 0 := by
    have h := herm_eq_zero hC.1.1 hc hc
    rw [herm_split, hA, herm_zero_left, zero_add] at h
    exact h
  obtain ⟨l, hl, hM⟩ := lemma23 (cB c) hB hiso
  have h16 := lemma22 hC.2.1 hC0 ((C1 C hg).smul_mem l hc) (smul_ne_zero hl hne)
  rw [cA_smul, cB_smul, hA, smul_zero, M_zero, zero_add] at h16
  omega

theorem herm_single : ∀ i j : Fin 7, herm (Pi.single i (1 : F16)) (Pi.single j 1) = if i = j then 1 else 0 := by
  decide +kernel

theorem F16_eq_of_add_eq_zero : ∀ a b : F16, a + b = 0 → b = a := by decide +kernel

/-- **The reduction to a unitary matrix.** In the layout of Sec. 2.2, `H_A` excludes an extremal code with the
automorphism `g5`. -/
theorem core (hA : H_A) (hC : Ext72 C) (hg : g5 ∈ Aut C) (hC0 : C0 C = e8e8w) : False := by
  let PA : C1 C hg → (Fin 7 → F16) := fun c => cA c.1
  have hinj : Function.Injective PA := by
    intro c c' h
    apply Subtype.ext
    have hd : c.1 - c'.1 ∈ C1 C hg := (C1 C hg).sub_mem c.2 c'.2
    have hA0 : cA (c.1 - c'.1) = 0 := by
      rw [cA_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (eq_zero_of_cA_eq_zero hC hC0 hd hA0)
  have hcard : Nat.card (Fin 7 → F16) ≤ Nat.card (C1 C hg) := by
    have h := card_C1_ge hC hg
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := F16), F16.card_eq, Nat.card_eq_fintype_card (α := Fin 7),
      Fintype.card_fin]
    norm_num at h ⊢
    exact h
  have hbij : Function.Bijective PA := hinj.bijective_of_nat_card_le hcard
  choose e he using fun i : Fin 7 => hbij.2 (Pi.single i 1)
  have heA : ∀ i, cA (e i).1 = Pi.single i 1 := he
  let U : Matrix (Fin 7) (Fin 7) F16 := fun i j => cB (e i).1 j
  have hU : U * Uᴴ = 1 := by
    ext i j
    have h0 := herm_eq_zero hC.1.1 (e i).2 (e j).2
    rw [herm_split, heA i, heA j, herm_single] at h0
    have h2 : herm (cB (e i).1) (cB (e j).1) = (U * Uᴴ) i j := by
      simp only [herm, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rfl
    rw [h2] at h0
    rw [Matrix.one_apply]
    exact F16_eq_of_add_eq_zero _ _ h0
  obtain ⟨a, ha, hlt⟩ := hA U hU
  have hca : (∑ i, a i • (e i).1) ∈ C1 C hg :=
    Submodule.sum_mem _ (fun i _ => (C1 C hg).smul_mem _ (e i).2)
  have hcaA : cA (∑ i, a i • (e i).1) = a := by
    funext k
    simp only [cA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h : ∀ i, (e i).1 (Fin.castAdd 7 k) = (Pi.single i (1 : F16) : Fin 7 → F16) k :=
      fun i => congrFun (heA i) k
    simp only [h, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcaB : cB (∑ i, a i • (e i).1) = a ᵥ* U := by
    funext j
    simp only [cB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
    rfl
  have hne : (∑ i, a i • (e i).1) ≠ 0 := fun h => ha (by rw [← hcaA, h]; rfl)
  have h16 := lemma22 hC.2.1 hC0 hca hne
  rw [hcaA, hcaB] at h16
  omega

end C72.T3

namespace C72

open Equiv Finset

/-- **Theorem A** from the named hypotheses `H_CP5`, `H_16` and `H_A`: a doubly-even self-dual `[72,36,16]`
code has no automorphism of order 5. -/
theorem thmA_of_hyps (h5 : H_CP5) (h16 : H_16) (hA : H_A) : ThmA := by
  intro C hC g hg hord
  obtain ⟨c, f, h, π, hf, hmem⟩ := exists_relabel (by norm_num : Nat.Prime 5) hg hord
  have hf2 : f = 2 := hf.trans (h5 C hC g hg hord)
  subst hf2
  have hc : c = 14 := by omega
  subst hc
  have hg5 : T3.g5 ∈ Aut (C.map (permute π).toLinearMap) := hmem
  obtain ⟨P, hP, hgP, hC0⟩ := T3.lemma21 h16 (hC.map_permute π) hg5
  exact T3.core hA hP hgP hC0

end C72
