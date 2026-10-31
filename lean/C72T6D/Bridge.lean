import C72T6.Search
import C72T4.Main

/-!
# T6, order 2: from the search to `H_D k` and Theorem D

`H_D_of_search` puts Lemma 6.3 (`lemma63_key`), Lemma 6.1 (b) and the slice property (`H_D_of_slice`) together. The facts
about the program are two hypotheses: `hrem`, the removal condition of Lemma 6.3 for the key of Section 6.2, and `hnone`,
"the search reports no solution": every form of `S_0 = A_0 ∩ slice` has a removed node among the nodes it extends (every
form is a leaf of the tree, `ext` is the prefix relation, and a leaf is reported unless one of its nodes is removed).
`thmD_of_search` gives Theorem D for `Y_k` (T4's `ThmD k`) from the same hypotheses.
-/

namespace C72.T6

open C72 C72.T4 Module Finset

/-- **From the search to `H_D k`** (Lemmas 6.1 (b), 6.3 and the slice property). -/
theorem H_D_of_search (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) {r : ℕ} {ms : Fin r → ℕ}
    (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ) (ks : Fin r → Yc k) (xss : ∀ i, Fin (ms i) → Yc k)
    (hdisj : ∀ i j l, (ks i : Fin 36 → ZMod 2) l = 0 ∨ (xss i j : Fin 36 → ZMod 2) l = 0)
    {N : Type*} (ext : LinearMap.BilinForm (ZMod 2) (Yc k) → N → Prop) (removed : N → Prop)
    (hrem : ∀ n, removed n → (∀ B, ext B n → ¬ IsSol k E B) ∨
      ∃ g : Aut (Yc k), ∀ B, ext B n → key rd ks xss (formAct g B) < key rd ks xss B)
    (hnone : ∀ B, InA0 (Yc k) (allOnes_mem_Yc k) B → B ∈ slice E → ∃ n, ext B n ∧ removed n) : H_D k := by
  refine H_D_of_slice k E (fun B hA hs => ?_)
  by_contra hnr
  obtain ⟨B', ⟨hA', hs', -⟩, hB'⟩ := lemma63_key k E rd ks xss hdisj ext removed hrem ⟨B, hA, hs, hnr⟩
  obtain ⟨n, hn, hrm⟩ := hnone B' hA' hs'
  exact hB' n hn hrm

/-- **Theorem D for `Y_k` from the search**: under the hypotheses of `H_D_of_search`, no extremal code has a
fixed-point-free involution whose contracted fixed code is equivalent to `Y_k`. -/
theorem thmD_of_search (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) {r : ℕ} {ms : Fin r → ℕ}
    (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ) (ks : Fin r → Yc k) (xss : ∀ i, Fin (ms i) → Yc k)
    (hdisj : ∀ i j l, (ks i : Fin 36 → ZMod 2) l = 0 ∨ (xss i j : Fin 36 → ZMod 2) l = 0)
    {N : Type*} (ext : LinearMap.BilinForm (ZMod 2) (Yc k) → N → Prop) (removed : N → Prop)
    (hrem : ∀ n, removed n → (∀ B, ext B n → ¬ IsSol k E B) ∨
      ∃ g : Aut (Yc k), ∀ B, ext B n → key rd ks xss (formAct g B) < key rd ks xss B)
    (hnone : ∀ B, InA0 (Yc k) (allOnes_mem_Yc k) B → B ∈ slice E → ∃ n, ext B n ∧ removed n) : ThmD k :=
  thmD_of_HD k (H_D_of_search k E rd ks xss hdisj ext removed hrem hnone)

end C72.T6
