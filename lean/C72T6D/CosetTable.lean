import C72T6.Search

/-!
# T6, order 2: the table of the coset rule

The paper's coset rule (Section 6.2) computes `s_{k₀ g}(B)` once for each coset `Γ₀ g` of the stabiliser `Γ₀` of `k₀` and
reads the values `s_{k₀}(B^h) = T_{h,k₀} s_{k₀ g}(B)`, `h ∈ Γ₀ g`, from a table. In Lean's product (`formAct_mul`: `g * σ`
acts on words as first `σ`, then `g`) the paper's coset `Γ₀ g` is `{g * σ : σ ∈ Γ₀}`, and `autLin (g * σ) k₀ = autLin g k₀`
for these (`syn_formAct_coset`). `coset_rule_table` derives the table values of `coset_rule` from the one vector
`v = s_{k₀ g}(B)`.
-/

namespace C72.T6

open C72 C72.T4 Module Finset

variable {ι : Type*} {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- For `σ` fixing `w`, `g * σ` lies in the paper's coset `Γ₀ g` (Lean's product: first `σ`, then `g`), and
`s_w(B^{g σ}) = T s_{w g}(B)` with the same vector `s_{w g}(B)` for every such `σ`. -/
theorem syn_formAct_coset {m m' : ℕ} (B : LinearMap.BilinForm (ZMod 2) Y) (g σ : Aut Y) (w : Y)
    (hσ : autLin σ w = w) (xs : Fin m → Y) (xs' : Fin m' → Y) (T : Matrix (Fin m) (Fin m') (ZMod 2))
    (hT : ∀ j, autLin (g * σ) (xs j) = ∑ l, T j l • xs' l) :
    syn (formAct (g * σ) B) w xs = T.mulVec (syn B (autLin g w) xs') := by
  rw [syn_formAct B (g * σ) w xs xs' T hT, autLin_mul, hσ]

/-- **The coset rule with its table** (Section 6.2). The node determines `v = s_{k₀ g}(B)`, computed once for the coset,
and the first key component `s₀` of `B`; for `σ ∈ S` (elements of the stabiliser of `k₀`) the table entry is the reading
of `T_σ v = s_{k₀}(B^{g σ})`. If the smallest entry is below `s₀`, one `g * σ` meets the removal condition of Lemma 6.3. -/
theorem coset_rule_table {N : Type*} {r m' : ℕ} {ms : Fin (r + 1) → ℕ} (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ)
    (ks : Fin (r + 1) → Y) (xss : ∀ i, Fin (ms i) → Y) (ext : LinearMap.BilinForm (ZMod 2) Y → N → Prop) (n : N)
    (g : Aut Y) (S : Finset (Aut Y)) (hS : S.Nonempty) (hstab : ∀ σ ∈ S, autLin σ (ks 0) = ks 0)
    (xs' : Fin m' → Y) (T : Aut Y → Matrix (Fin (ms 0)) (Fin m') (ZMod 2))
    (hT : ∀ σ ∈ S, ∀ j, autLin (g * σ) (xss 0 j) = ∑ l, T σ j l • xs' l)
    (v : Fin m' → ZMod 2) (hv : ∀ B, ext B n → syn B (autLin g (ks 0)) xs' = v)
    (s₀ : ℕ) (hs₀ : ∀ B, ext B n → rd 0 (syn B (ks 0) (xss 0)) = s₀)
    (hmin : S.inf' hS (fun σ => rd 0 ((T σ).mulVec v)) < s₀) :
    ∃ σ ∈ S, ∀ B, ext B n → key rd ks xss (formAct (g * σ) B) < key rd ks xss B := by
  obtain ⟨σ, hσS, h⟩ := coset_rule ext n (fun σ B => formAct (g * σ) B)
    (fun B i => rd i (syn B (ks i) (xss i))) S hS (fun σ => rd 0 ((T σ).mulVec v)) s₀
    (fun σ hσ B hB => by
      show rd 0 (syn (formAct (g * σ) B) (ks 0) (xss 0)) = rd 0 ((T σ).mulVec v)
      rw [syn_formAct_coset B g σ (ks 0) (hstab σ hσ) (xss 0) xs' (T σ) (hT σ hσ), hv B hB])
    hs₀ hmin
  exact ⟨σ, hσS, h⟩

end C72.T6
