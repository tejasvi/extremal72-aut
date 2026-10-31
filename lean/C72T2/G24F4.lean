import C72T2.Golay
import C72T2.Hermitian

/-!
# T2: the antecedents of `H_LP` and `H_CB` are satisfiable (`G24 ⊗ 𝔽₄`)

`G24F4`, the `𝔽₄`-span of the binary extended Golay code (Section 5 of the paper), is Hermitian self-dual, has minimum weight
at least 8 and has a word of weight 8 (`G24F4_antecedent`). So the hypotheses that `H_LP` and `H_CB` put on `E` can
be met, and these named hypotheses are not vacuous at length 24.

With `ι : 𝔽₂ → 𝔽₄` the inclusion applied coordinatewise (`incl`), every word of `G24F4` is `ι a + ω ι b` with
`a, b ∈ G24` (`mem_G24F4_iff`), its support is `supp a ∪ supp b` (`supp_incl_add`), and a word `ι a + ω ι b` is
Hermitian-orthogonal to `ι g` exactly when `a` and `b` are orthogonal to `g`; no enumeration of the `4¹²` words is
needed.
-/

namespace C72.Three

open Finset F4

/-- The inclusion `𝔽₂ → 𝔽₄`. -/
def incl1 (x : ZMod 2) : F4 :=
  if x = 0 then 0 else 1

/-- The inclusion `ι`, applied coordinatewise. -/
def incl (x : Fin 24 → ZMod 2) : Fin 24 → F4 :=
  fun i => incl1 (x i)

theorem incl1_add : ∀ x y : ZMod 2, incl1 (x + y) = incl1 x + incl1 y := by
  decide

theorem incl_add (x y : Fin 24 → ZMod 2) : incl (x + y) = incl x + incl y :=
  funext fun i => incl1_add (x i) (y i)

theorem incl_zero : incl 0 = 0 :=
  funext fun _ => rfl

/-- `ι` as an additive map, for sums. -/
def incl1Hom : ZMod 2 →+ F4 :=
  AddMonoidHom.mk' incl1 incl1_add

/-- `G24 ⊗ 𝔽₄`: the `𝔽₄`-span of the generators of `G24`. -/
def G24F4 : Submodule F4 (Fin 24 → F4) :=
  Submodule.span F4 (Set.range fun s => incl (g24gen s))

/-- The words `ι a + ω ι b` with `a, b ∈ G24`, an `𝔽₄`-submodule. -/
def G24F4' : Submodule F4 (Fin 24 → F4) where
  carrier := {e | ∃ a ∈ G24, ∃ b ∈ G24, incl a + F4.w • incl b = e}
  zero_mem' := ⟨0, G24.zero_mem, 0, G24.zero_mem, by rw [incl_zero, smul_zero, add_zero]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a + a', G24.add_mem ha ha', b + b', G24.add_mem hb hb', ?_⟩
    rw [incl_add, incl_add, smul_add]
    abel
  smul_mem' := by
    rintro c _ ⟨a, ha, b, hb, rfl⟩
    have k0 : ∀ x y : ZMod 2, incl1 0 + F4.w * incl1 0 = F4.zero * (incl1 x + F4.w * incl1 y) := by decide
    have k1 : ∀ x y : ZMod 2, incl1 x + F4.w * incl1 y = F4.one * (incl1 x + F4.w * incl1 y) := by decide
    have kw : ∀ x y : ZMod 2, incl1 y + F4.w * incl1 (x + y) = F4.w * (incl1 x + F4.w * incl1 y) := by
      decide
    have kwb : ∀ x y : ZMod 2, incl1 (x + y) + F4.w * incl1 x = F4.wb * (incl1 x + F4.w * incl1 y) := by
      decide
    cases c
    · refine ⟨0, G24.zero_mem, 0, G24.zero_mem, funext fun i => ?_⟩
      exact k0 (a i) (b i)
    · refine ⟨a, ha, b, hb, funext fun i => ?_⟩
      exact k1 (a i) (b i)
    · refine ⟨b, hb, a + b, G24.add_mem ha hb, funext fun i => ?_⟩
      exact kw (a i) (b i)
    · refine ⟨a + b, G24.add_mem ha hb, a, ha, funext fun i => ?_⟩
      exact kwb (a i) (b i)

theorem incl_mem_G24F4 {a : Fin 24 → ZMod 2} (ha : a ∈ G24) : incl a ∈ G24F4 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Submodule.subset_span ⟨s, rfl⟩
  | zero => rw [incl_zero]; exact G24F4.zero_mem
  | add x y _ _ hx hy => rw [incl_add]; exact G24F4.add_mem hx hy
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, incl_zero]
      exact G24F4.zero_mem
    · rw [one_smul]
      exact hx

theorem G24F4_eq : G24F4 = G24F4' := by
  apply le_antisymm
  · rw [G24F4, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact ⟨g24gen s, Submodule.subset_span ⟨s, rfl⟩, 0, G24.zero_mem, by rw [incl_zero, smul_zero, add_zero]⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact G24F4.add_mem (incl_mem_G24F4 ha) (G24F4.smul_mem F4.w (incl_mem_G24F4 hb))

/-- Every word of `G24 ⊗ 𝔽₄` is `ι a + ω ι b` with `a, b ∈ G24`. -/
theorem mem_G24F4_iff {e : Fin 24 → F4} : e ∈ G24F4 ↔ ∃ a ∈ G24, ∃ b ∈ G24, incl a + F4.w • incl b = e := by
  rw [G24F4_eq]
  rfl

/-- `supp (ι a + ω ι b) = supp a ∪ supp b`. -/
theorem supp_incl_add (a b : Fin 24 → ZMod 2) : supp (incl a + F4.w • incl b) = supp a ∪ supp b := by
  ext i
  rw [Finset.mem_union, mem_supp, mem_supp, mem_supp]
  have key : ∀ x y : ZMod 2, incl1 x + F4.w * incl1 y ≠ 0 ↔ x ≠ 0 ∨ y ≠ 0 := by decide
  exact key (a i) (b i)

/-- The generators are pairwise Hermitian-orthogonal. -/
theorem incl_gen_orth : ∀ s t : Fin 12, hform (incl (g24gen s)) (incl (g24gen t)) = 0 := by
  decide +kernel

theorem incl1_star : ∀ y : ZMod 2, star (incl1 y) = incl1 y := by
  decide

theorem incl1_mul : ∀ p q y : ZMod 2,
    (incl1 p + F4.w * incl1 q) * incl1 y = incl1 (p * y) + F4.w * incl1 (q * y) := by
  decide

theorem incl1_indep : ∀ p q : ZMod 2, incl1 p + F4.w * incl1 q = 0 → p = 0 ∧ q = 0 := by
  decide

/-- The coordinates of `z = ι(re z) + ω ι(im z)` over `{1, ω}`. -/
def re4 (z : F4) : ZMod 2 :=
  if z = 1 ∨ z = F4.wb then 1 else 0

def im4 (z : F4) : ZMod 2 :=
  if z = F4.w ∨ z = F4.wb then 1 else 0

theorem incl1_split : ∀ z : F4, incl1 (re4 z) + F4.w * incl1 (im4 z) = z := by
  decide

theorem incl1_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) : ∑ i ∈ s, incl1 (f i) = incl1 (∑ i ∈ s, f i) :=
  (map_sum incl1Hom f s).symm

/-- `⟨ι a + ω ι b, ι g⟩_H = ι⟨a, g⟩ + ω ι⟨b, g⟩` for binary `a`, `b`, `g`. -/
theorem hform_incl (a b g : Fin 24 → ZMod 2) :
    hform (incl a + F4.w • incl b) (incl g) = incl1 (a ⬝ᵥ g) + F4.w * incl1 (b ⬝ᵥ g) := by
  have hpt : ∀ i, (incl a + F4.w • incl b) i * star (incl g i) =
      incl1 (a i * g i) + F4.w * incl1 (b i * g i) := fun i => by
    show (incl1 (a i) + F4.w * incl1 (b i)) * star (incl1 (g i)) = _
    rw [incl1_star, incl1_mul]
  rw [hform, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, ← Finset.mul_sum, incl1_sum,
    incl1_sum]
  rfl

theorem G24F4_le_hdual : G24F4 ≤ hdual G24F4 := by
  rw [G24F4, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, mem_hdual_span]
  rintro _ ⟨t, rfl⟩
  exact incl_gen_orth s t

theorem hdual_G24F4_le : hdual G24F4 ≤ G24F4 := by
  intro x hx
  rw [G24F4, mem_hdual_span] at hx
  have hx' : incl (fun i => re4 (x i)) + F4.w • incl (fun i => im4 (x i)) = x :=
    funext fun i => incl1_split (x i)
  have horth : ∀ t : Fin 12,
      (fun i => re4 (x i)) ⬝ᵥ g24gen t = 0 ∧ (fun i => im4 (x i)) ⬝ᵥ g24gen t = 0 := fun t => by
    have h := hx _ ⟨t, rfl⟩
    rw [← hx', hform_incl] at h
    exact incl1_indep _ _ h
  rw [← hx', mem_G24F4_iff]
  exact ⟨_, mem_G24_of_orth fun t => (horth t).1, _, mem_G24_of_orth fun t => (horth t).2, rfl⟩

theorem G24F4_minWt : ∀ e ∈ G24F4, e ≠ 0 → 8 ≤ wt e := by
  intro e he hne
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_G24F4_iff.1 he
  rw [← card_supp, supp_incl_add]
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      rintro rfl
      apply hne
      rw [ha0, incl_zero, smul_zero, add_zero]
    have h8 := G24_minWt b hb hb0
    rw [← card_supp] at h8
    exact le_trans h8 (Finset.card_le_card Finset.subset_union_right)
  · have h8 := G24_minWt a ha ha0
    rw [← card_supp] at h8
    exact le_trans h8 (Finset.card_le_card Finset.subset_union_left)

theorem G24F4_wt8 : ∃ e ∈ G24F4, wt e = 8 := by
  have hw : wt (incl (g24gen 0)) = 8 := by
    decide +kernel
  exact ⟨incl (g24gen 0), Submodule.subset_span ⟨0, rfl⟩, hw⟩

/-- **`G24 ⊗ 𝔽₄` is Hermitian self-dual, with minimum weight at least 8 and a word of weight 8.** -/
theorem G24F4_antecedent : HSelfDual G24F4 ∧ (∀ e ∈ G24F4, e ≠ 0 → 8 ≤ wt e) ∧ ∃ e ∈ G24F4, wt e = 8 :=
  ⟨le_antisymm G24F4_le_hdual hdual_G24F4_le, G24F4_minWt, G24F4_wt8⟩

end C72.Three
