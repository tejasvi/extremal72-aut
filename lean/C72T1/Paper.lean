import C72T1.Final

/-!
# The paper-form statements

The paper's notions written with Mathlib primitives only, the proofs that `Ext72` and `Aut` agree with them in both
directions, the paper's Main Theorem in this form from `main_of_cited`, and two facts about the named hypotheses:
`H_primes` follows from the order list of [Bor15, Thm 6.3], and every named hypothesis holds when no extremal code
exists (none has content outside the extremal codes).

These statements were written independently of the rest of the development, as a check that `Ext72` and
`Aut` say what the paper says; they use only notions that Mathlib defines.
The binder `p` of `H_primes_of_orders` is written `_p`, since the statement does not use it and the
unused-variable linter would flag it.
-/

namespace C72

/-! ## 2. The paper's notions from Mathlib primitives -/

/-- The paper's hypotheses on `C` (Section 1): `C = C^⊥` written out, dimension 36, doubly-even, minimum weight
exactly 16. -/
def PaperExt72 (C : Submodule (ZMod 2) (Fin 72 → ZMod 2)) : Prop :=
  (∀ x : Fin 72 → ZMod 2, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) ∧ Module.finrank (ZMod 2) C = 36 ∧
    (∀ x ∈ C, 4 ∣ hammingNorm x) ∧ (∀ x ∈ C, x ≠ 0 → 16 ≤ hammingNorm x) ∧
      ∃ x ∈ C, hammingNorm x = 16

/-- The paper's `Aut(C)`: the permutations `p` with `Cp = C`, where `(xp)_{p(i)} = x_i`, i.e. `xp = x ∘ p⁻¹`. -/
def PaperAut (C : Submodule (ZMod 2) (Fin 72 → ZMod 2)) : Set (Equiv.Perm (Fin 72)) :=
  {p | (fun (x : Fin 72 → ZMod 2) => fun i => x (p⁻¹ i)) '' (C : Set (Fin 72 → ZMod 2)) =
    (C : Set (Fin 72 → ZMod 2))}

/-- The action used in `PaperAut` is the paper's: `xp` has `x_i` at the coordinate `p(i)`. -/
theorem paper_action (p : Equiv.Perm (Fin 72)) (x : Fin 72 → ZMod 2) (i : Fin 72) :
    (fun j => x (p⁻¹ j)) (p i) = x i :=
  congrArg x (Equiv.symm_apply_apply p i)

/-- `Ext72` is exactly the paper's notion. -/
theorem ext72_iff_paper (C : C72.Code 72) : C72.Ext72 C ↔ PaperExt72 C := by
  constructor
  · intro hC
    have hsd : C = C72.dual C := hC.1.1
    refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, C72.Ext72.finrank hC, hC.1.2, hC.2.1, hC.2.2⟩
    · rw [hsd] at hx
      exact hx
    · have hx' : x ∈ C72.dual C := hx
      rw [← hsd] at hx'
      exact hx'
  · rintro ⟨hsd, _hdim, hde, hmin, hex⟩
    refine ⟨⟨?_, hde⟩, hmin, hex⟩
    show C = C72.dual C
    ext x
    exact hsd x

/-- `Aut` is exactly the paper's `Aut(C)`. -/
theorem mem_Aut_iff_paper (C : C72.Code 72) (p : Equiv.Perm (Fin 72)) :
    p ∈ C72.Aut C ↔ p ∈ PaperAut C := by
  constructor
  · intro hp
    have h := SetLike.ext'_iff.1 (C72.mem_Aut.1 hp)
    rw [Submodule.map_coe] at h
    show (fun (x : Fin 72 → ZMod 2) => fun i => x (p⁻¹ i)) '' (C : Set (Fin 72 → ZMod 2)) =
      (C : Set (Fin 72 → ZMod 2))
    exact h
  · intro hp
    refine C72.mem_Aut.2 (SetLike.ext' ?_)
    rw [Submodule.map_coe]
    exact hp

/-- The paper's Main Theorem with the paper's notions only. -/
def PaperMain : Prop :=
  ∀ C : Submodule (ZMod 2) (Fin 72 → ZMod 2), PaperExt72 C → PaperAut C = {1}

theorem paperMain_of_cited (h1 : C72.H_primes) (hL1 : C72.H_L1) (hA : C72.ThmA) (hB : C72.ThmB)
    (hD : C72.NoFPFInv) : PaperMain := by
  intro C hC
  have hbot : C72.Aut C = ⊥ := C72.main_of_cited h1 hL1 hA hB hD C ((ext72_iff_paper C).2 hC)
  ext p
  rw [Set.mem_singleton_iff, ← mem_Aut_iff_paper, hbot, Subgroup.mem_bot]

/-! ## The named hypotheses -/

theorem primes_of_order_le_five {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) (hd : p ∣ n) : p = 2 ∨ p = 3 ∨ p = 5 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact absurd (Nat.dvd_one.1 hd) hp.ne_one
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd))
  · have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hd
    have h2 := hp.two_le
    have hcases : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hd (by decide)
    · rcases hp.eq_one_or_self_of_dvd 2 (by decide) with h | h <;> omega
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd))

/-- `H_primes` is implied by the order list of [Bor15, Thm 6.3]: `|Aut C|` is 1, 2, 3, 4 or 5. -/
theorem H_primes_of_orders (h : ∀ C : C72.Code 72, C72.Ext72 C →
    Nat.card (C72.Aut C) = 1 ∨ Nat.card (C72.Aut C) = 2 ∨ Nat.card (C72.Aut C) = 3 ∨
      Nat.card (C72.Aut C) = 4 ∨ Nat.card (C72.Aut C) = 5) : C72.H_primes :=
  fun C hC _p hp hd => primes_of_order_le_five hp (h C hC) hd

/-- Every named hypothesis holds when no extremal code exists: none has content outside the extremal codes. -/
theorem hyps_of_no_extremal (h : ¬ ∃ C : C72.Code 72, C72.Ext72 C) :
    C72.H_primes ∧ C72.H_L1 ∧ C72.ThmA ∧ C72.ThmB ∧ C72.NoFPFInv :=
  ⟨fun C hC => (h ⟨C, hC⟩).elim, fun C hC => (h ⟨C, hC⟩).elim, fun C hC => (h ⟨C, hC⟩).elim,
    fun C hC => (h ⟨C, hC⟩).elim, fun C hC => (h ⟨C, hC⟩).elim⟩

end C72
