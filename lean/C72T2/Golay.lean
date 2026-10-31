import C72T2.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# T2: the reference extended Golay code `G24`

`G24` is the code of the labelling programs (`order3/labelling/point_placement/src/csp5p.c`, `qr_golay_gen`):
row `s` (`0 ≤ s ≤ 11`) of its generator matrix is `x^s g(x)` with `g(x) = 1 + x² + x⁴ + x⁵ + x⁶ + x¹⁰ + x¹¹` (the
cyclic `[23,12,7]` quadratic residue code), extended by the parity bit 23. The generators are given by bit masks
(`g24mask`, bit `i` is coordinate `i`); `g24gen_spec` restates them as `qr_golay_gen` does. The octads and
dodecads of `G24` are the supports of its words of weight 8 and 12 (`IsOctad`, `IsDodecad`); `C72T2.OctDod`
proves that they are exactly the entries of the program's `octdod.txt` (`isOctad_iff`, `isDodecad_iff`).

Checked here, by one kernel evaluation over all `2¹² = 4096` coefficient vectors (`g24_chk`, a Bool-valued
recursion `chk` with the soundness lemma `chk_sound`): every nonzero combination of the generators has weight
8, 12, 16 or 24. Hence the generators are independent (`finrank_G24 = 12`), the weights of `G24` are
`0, 8, 12, 16, 24` (`G24_wt`), and with the Gram matrix of the generators (`g24gen_orth`) `G24` is Type II with
minimum weight 8 (`G24_typeII`, `G24_minWt`, `G24_wt8`).
-/

namespace C72.Three

open Finset Module

/-! ## Words from bit masks -/

/-- The binary word of length 24 whose support is the set of bits of `m` (bit `i` is coordinate `i`). -/
def toVec (m : ℕ) : Fin 24 → ZMod 2 :=
  fun i => if m.testBit i.val then 1 else 0

theorem toVec_zero : toVec 0 = 0 := by
  funext i
  simp [toVec]

theorem toVec_xor (a b : ℕ) : toVec (a ^^^ b) = toVec a + toVec b := by
  funext i
  simp only [toVec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

/-! ## The code -/

/-- Bit masks of the 12 generators of `G24` (`qr_golay_gen` in `csp5p.c`). -/
def g24mask : Fin 12 → ℕ :=
  ![8391797, 8394986, 8401364, 8414120, 8439632, 8490656, 8592704, 8796800, 9204992, 10021376, 11654144,
    14919680]

/-- The generators of `G24`. -/
def g24gen (s : Fin 12) : Fin 24 → ZMod 2 :=
  toVec (g24mask s)

/-- The reference extended Golay code. -/
def G24 : Code 24 :=
  Submodule.span (ZMod 2) (Set.range g24gen)

/-- The generators as `qr_golay_gen` builds them: row `s` has support `{s + j | j ∈ {0, 2, 4, 5, 6, 10, 11}}`
(the word `x^s g(x)`) together with the parity coordinate 23. -/
theorem g24gen_spec : ∀ (s : Fin 12) (i : Fin 24), g24gen s i =
    if (s.val ≤ i.val ∧ i.val - s.val ∈ ({0, 2, 4, 5, 6, 10, 11} : Finset ℕ)) ∨ i.val = 23 then 1 else 0 := by
  decide +kernel

/-! ## The check over all 4096 words -/

/-- The nonzero weights of the extended Golay code. -/
def okWt (n : ℕ) : Bool :=
  n == 8 || n == 12 || n == 16 || n == 24

theorem okWt_iff {n : ℕ} : okWt n = true ↔ n = 8 ∨ n = 12 ∨ n = 16 ∨ n = 24 := by
  simp [okWt, or_assoc]

/-- `chk k ms nz acc` checks, for every `c ∈ 𝔽₂ᵏ`, that the word with bit mask `acc ⊕ ⨁_{c_j = 1} ms_j` has
weight 8, 12, 16 or 24; the case `c = 0` is skipped when `nz = false`. -/
def chk : (k : ℕ) → (Fin k → ℕ) → Bool → ℕ → Bool
  | 0, _, nz, acc => !nz || okWt (wt (toVec acc))
  | k + 1, ms, nz, acc => chk k (Fin.tail ms) nz acc && chk k (Fin.tail ms) true (acc ^^^ ms 0)

/-- Soundness of `chk`. -/
theorem chk_sound : ∀ (k : ℕ) (ms : Fin k → ℕ) (nz : Bool) (acc : ℕ), chk k ms nz acc = true →
    ∀ c : Fin k → ZMod 2, (nz = true ∨ c ≠ 0) →
      okWt (wt (toVec acc + ∑ j, c j • toVec (ms j))) = true := by
  intro k
  induction k with
  | zero =>
    intro ms nz acc h c hc
    have hc0 : c = 0 := funext fun j => j.elim0
    rcases hc with hnz | hne
    · simp only [chk, hnz, Bool.not_true, Bool.false_or] at h
      simpa using h
    · exact absurd hc0 hne
  | succ k ih =>
    intro ms nz acc h c hc
    simp only [chk, Bool.and_eq_true] at h
    rw [Fin.sum_univ_succ]
    rcases zmod2_cases (c 0) with h0 | h1
    · rw [h0, zero_smul, zero_add]
      have hc' : nz = true ∨ Fin.tail c ≠ 0 := by
        rcases hc with hnz | hne
        · exact Or.inl hnz
        · right
          intro ht
          apply hne
          funext j
          refine Fin.cases ?_ (fun j => ?_) j
          · exact h0
          · exact congrFun ht j
      exact ih (Fin.tail ms) nz acc h.1 (Fin.tail c) hc'
    · rw [h1, one_smul, ← add_assoc, ← toVec_xor]
      exact ih (Fin.tail ms) true (acc ^^^ ms 0) h.2 (Fin.tail c) (Or.inl rfl)

/-- **The kernel check over the 4096 words of `G24`.** -/
theorem g24_chk : chk 12 g24mask false 0 = true := by
  decide +kernel

/-- Every nonzero combination of the generators has weight 8, 12, 16 or 24. -/
theorem g24_okWt {c : Fin 12 → ZMod 2} (hc : c ≠ 0) : okWt (wt (∑ j, c j • g24gen j)) = true := by
  have h := chk_sound 12 g24mask false 0 g24_chk c (Or.inr hc)
  simpa [toVec_zero, g24gen] using h

/-! ## Consequences -/

theorem mem_G24 {x : Fin 24 → ZMod 2} : x ∈ G24 ↔ ∃ c : Fin 12 → ZMod 2, ∑ j, c j • g24gen j = x :=
  Submodule.mem_span_range_iff_exists_fun (ZMod 2)

/-- The weights of `G24` are `0, 8, 12, 16, 24`. -/
theorem G24_wt {x : Fin 24 → ZMod 2} (hx : x ∈ G24) :
    wt x = 0 ∨ wt x = 8 ∨ wt x = 12 ∨ wt x = 16 ∨ wt x = 24 := by
  obtain ⟨c, rfl⟩ := mem_G24.1 hx
  by_cases hc : c = 0
  · left
    subst hc
    simp [wt_zero]
  · right
    exact okWt_iff.1 (g24_okWt hc)

theorem g24gen_linearIndependent : LinearIndependent (ZMod 2) g24gen := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  have hc' : c ≠ 0 := fun h => hi (congrFun h i)
  have h := g24_okWt hc'
  rw [hc, wt_zero] at h
  exact absurd h (by decide)

theorem finrank_G24 : finrank (ZMod 2) G24 = 12 := by
  rw [G24, finrank_span_eq_card g24gen_linearIndependent, Fintype.card_fin]

/-- The generators are pairwise orthogonal (the Gram matrix is zero). -/
theorem g24gen_orth : ∀ i j : Fin 12, g24gen i ⬝ᵥ g24gen j = 0 := by
  decide +kernel

theorem G24_le_dual : G24 ≤ dual G24 := by
  rw [G24, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨j, rfl⟩
  exact g24gen_orth i j

theorem G24_selfDual : SelfDual G24 :=
  selfDual_of_le_of_two_mul_finrank G24_le_dual (by rw [finrank_G24, Fintype.card_fin])

/-- `x ∈ G24` as soon as `x` is orthogonal to the 12 generators (`G24` is self-dual). -/
theorem mem_G24_of_orth {x : Fin 24 → ZMod 2} (h : ∀ j, x ⬝ᵥ g24gen j = 0) : x ∈ G24 := by
  rw [G24_selfDual, G24, mem_dual_span]
  rintro _ ⟨j, rfl⟩
  exact h j

/-- `G24` is Type II. -/
theorem G24_typeII : TypeII G24 := by
  refine ⟨G24_selfDual, fun x hx => ?_⟩
  rcases G24_wt hx with h | h | h | h | h <;> rw [h] <;> decide

/-- `G24` has minimum weight at least 8. -/
theorem G24_minWt : MinWt G24 8 := by
  intro x hx hne
  have h0 : wt x ≠ 0 := fun h => hne (wt_eq_zero.1 h)
  rcases G24_wt hx with h | h | h | h | h <;> omega

/-- `G24` has a word of weight 8. -/
theorem G24_wt8 : ∃ x ∈ G24, wt x = 8 :=
  ⟨g24gen 0, Submodule.subset_span ⟨0, rfl⟩, by decide +kernel⟩

/-- An octad of `G24`: the support of a word of weight 8. -/
def IsOctad (O : Finset (Fin 24)) : Prop :=
  ∃ x ∈ G24, wt x = 8 ∧ supp x = O

/-- A dodecad of `G24`: the support of a word of weight 12. -/
def IsDodecad (D : Finset (Fin 24)) : Prop :=
  ∃ x ∈ G24, wt x = 12 ∧ supp x = D

end C72.Three
