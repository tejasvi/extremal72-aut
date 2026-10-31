import C72T6.Slice
import Mathlib.Data.DFinsupp.WellFounded

/-!
# T6: Lemma 6.3, the soundness of the symmetry pruning

**Abstract form** (`lemma63_abstract`). Forms `F`, nodes `N` of the search tree (`ext B n`: the form `B` extends the
node `n`), solutions `sol`, a group `Γ` acting on forms, the representative `rep` of a form in the slice, and a key
`K` with values in a well-founded linear order. If the slice representative of `B^g` is a solution whenever `B` is,
`K` takes the same value on `B^g` and its representative, and the search removes a node only when every extension
violates a constraint or when some `g` has `K(B^g) < K(B)` for every extension `B`, then: if a solution exists, some
solution has no removed node on its path, so the search reports it (proof of the paper: a solution with minimal key).

**Order 2** (`lemma63_order2`). For `Y_k`, the forms of `A_0(Y_k)`, the slice of an echelon basis of `G_0`, solutions
`B ∈ S_0` that are not ruled out, and the action `B^g(x, x') = B(x g, x' g)` of `Aut(Y_k)`: the hypotheses of the abstract
form hold for every key constant on the cosets of `G_0`. The action preserves `A_0` (`InA0_formAct`) and `G_0`
(`formAct_DT`: `D_T^g = D_{T g⁻¹}`; `formAct_mem_G0`), so it permutes the cosets of `G_0` in `A_0`, and it maps solutions
to solutions (`ruledOut_of_ruledOut_formAct`).

**The program's tests** (Section 6.2). The key `K(B)` is the tuple of the syndromes of the key words, each read as a
number, compared lexicographically (`key`, in `Lex (Fin r → ℕ)`). It is constant on the cosets of `G_0` (`syn_add`,
`key_add`, by Lemma 6.1 (b)), so Lemma 6.3 holds with this key (`lemma63_key`). Each test removes a node only under the
condition of Lemma 6.3: the first test when the first difference of the two keys is smaller (`first_test`,
`key_lt_of_first_diff`), and for the first component through the coset rule (`coset_rule`: the `h` that attains the
table minimum works for every extension); the second test when the leading bits of the first component are smaller
(`second_test`, `lt_of_leading_bits_lt`). The table values rest on `s_w(B^g) = T_{g,w} s_{wg}(B)` (`syn_formAct`) and on
`B^{g σ} = (B^g)^σ` in Lean's product (`formAct_mul`).
-/

namespace C72.T6

open C72 C72.T4 Module Finset

/-! ## The abstract lemma -/

/-- **Lemma 6.3, abstract form.** -/
theorem lemma63_abstract {F N Γ κ : Type*} [LinearOrder κ] [WellFoundedLT κ]
    (ext : F → N → Prop) (sol : F → Prop) (removed : N → Prop) (act : Γ → F → F) (K : F → κ) (rep : F → F)
    (hsol : ∀ g B, sol B → sol (rep (act g B))) (hK : ∀ g B, K (rep (act g B)) = K (act g B))
    (hrem : ∀ n, removed n → (∀ B, ext B n → ¬ sol B) ∨ ∃ g, ∀ B, ext B n → K (act g B) < K B)
    (hex : ∃ B, sol B) : ∃ B, sol B ∧ ∀ n, ext B n → ¬ removed n := by
  obtain ⟨B₀, hB₀⟩ := hex
  let B := Function.argminOn K {B | sol B} ⟨B₀, hB₀⟩
  have hB : sol B := Function.argminOn_mem K {B | sol B} ⟨B₀, hB₀⟩
  have hmin : ∀ B', sol B' → K B ≤ K B' := fun B' hB' => by
    have := Function.argminOn_le K {B | sol B} (a := B') hB'
    exact this
  refine ⟨B, hB, fun n hn hrm => ?_⟩
  rcases hrem n hrm with h | ⟨g, hg⟩
  · exact h B hn hB
  · have h1 := hg B hn
    have h2 := hmin _ (hsol g B hB)
    rw [hK] at h2
    exact absurd h1 (not_lt.2 h2)

/-! ## The action of `Aut(Y)` on forms -/

variable {ι : Type*} {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- `x ↦ x g` on `Y`, for `g ∈ Aut Y`. -/
def autLin (g : Aut Y) : Y →ₗ[ZMod 2] Y :=
  (permute (g : Equiv.Perm ι)).toLinearMap.restrict (fun _ hx => permute_mem_of_mem_Aut g.2 hx)

theorem autLin_coe (g : Aut Y) (x : Y) : (autLin g x : ι → ZMod 2) = permute (g : Equiv.Perm ι) x :=
  rfl

theorem autLin_mul (g h : Aut Y) (x : Y) : autLin (g * h) x = autLin g (autLin h x) :=
  rfl

theorem autLin_inv_apply (g : Aut Y) (x : Y) : autLin g (autLin g⁻¹ x) = x := by
  apply Subtype.ext
  rw [autLin_coe, autLin_coe]
  show permute (g : Equiv.Perm ι) (permute (g : Equiv.Perm ι)⁻¹ (x : ι → ZMod 2)) = (x : ι → ZMod 2)
  rw [← permute_mul, mul_inv_cancel, permute_one_apply]

/-- `B^g(x, x') = B(x g, x' g)`. -/
def formAct (g : Aut Y) (B : LinearMap.BilinForm (ZMod 2) Y) : LinearMap.BilinForm (ZMod 2) Y :=
  B.compl₁₂ (autLin g) (autLin g)

theorem formAct_apply (g : Aut Y) (B : LinearMap.BilinForm (ZMod 2) Y) (x x' : Y) :
    formAct g B x x' = B (autLin g x) (autLin g x') :=
  rfl

/-- `B^{g h} = (B^g)^h` in Lean's product (first `h`, then `g` on words). -/
theorem formAct_mul (g h : Aut Y) (B : LinearMap.BilinForm (ZMod 2) Y) :
    formAct (g * h) B = formAct h (formAct g B) :=
  rfl

theorem autLin_allOnes (g : Aut Y) (h1 : allOnes ∈ Y) : autLin g ⟨allOnes, h1⟩ = ⟨allOnes, h1⟩ :=
  Subtype.ext rfl

/-- `B ↦ B^g` preserves `A_0`. -/
theorem InA0_formAct [Fintype ι] {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y} (hB : InA0 Y h1 B)
    (g : Aut Y) :
    InA0 Y h1 (formAct g B) := by
  refine ⟨fun y y' => ?_, fun y => ?_⟩
  · rw [formAct_apply, formAct_apply, hB.1]
  · rw [formAct_apply, formAct_apply, hB.2 (autLin g y), autLin_allOnes, autLin_coe, wt_permute]

theorem formAct_add (g : Aut Y) (B D : LinearMap.BilinForm (ZMod 2) Y) :
    formAct g (B + D) = formAct g B + formAct g D := by
  ext x x'
  rfl

/-- `D_T^g = D_{T g⁻¹}`. -/
theorem formAct_DT (g : Aut Y) (T : Finset ι) :
    formAct g (DT Y T) = DT Y (T.map (g : Equiv.Perm ι).symm.toEmbedding) := by
  ext x x'
  rw [formAct_apply, DT_apply, DT_apply, autLin_coe, autLin_coe, Finset.sum_map]
  simp only [permute_apply, Equiv.toEmbedding_apply]

/-- `B ↦ B^g` maps `G_0` into itself, so it permutes the cosets of `G_0`. -/
theorem formAct_mem_G0 (g : Aut Y) : ∀ D ∈ G0 Y, formAct g D ∈ G0 Y := by
  apply G0_induction
  · intro T
    rw [formAct_DT]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have h0 : formAct g (0 : LinearMap.BilinForm (ZMod 2) Y) = 0 := by
      ext x x'
      rfl
    rw [h0]
    exact Submodule.zero_mem _
  · intro D D' h h'
    rw [formAct_add]
    exact Submodule.add_mem _ h h'
  · intro a D h
    have hs : formAct g (a • D) = a • formAct g D := by
      ext x x'
      rfl
    rw [hs]
    exact Submodule.smul_mem _ a h

theorem indicator_map [DecidableEq ι] (g : Equiv.Perm ι) (e : Finset ι) :
    indicator (e.map g.toEmbedding) = permute g (indicator e) := by
  funext i
  simp only [indicator, permute_apply, Finset.mem_map_equiv]

/-- If `B^g` is ruled out (at the word `y`), then `B` is ruled out (at the word `y g`). -/
theorem ruledOut_of_ruledOut_formAct [Fintype ι] [DecidableEq ι] {B : LinearMap.BilinForm (ZMod 2) Y} (g : Aut Y)
    (h : RuledOut Y (formAct g B)) : RuledOut Y B := by
  obtain ⟨y, hy, e, he, hcard, hsyn⟩ := h
  refine ⟨autLin g y, ?_, e.map (g : Equiv.Perm ι).toEmbedding, ?_, ?_, ?_⟩
  · unfold IsConstraint at hy ⊢
    rw [autLin_coe, wt_permute]
    exact hy
  · intro i hi
    rw [Finset.mem_map_equiv] at hi
    rw [autLin_coe, permute_apply]
    exact he _ hi
  · rw [Finset.card_map, autLin_coe, wt_permute]
    exact hcard
  · intro x hx
    have hx0 : ∀ i, (y : ι → ZMod 2) i = 0 ∨ (autLin g⁻¹ x : ι → ZMod 2) i = 0 := by
      intro i
      have := hx ((g : Equiv.Perm ι) i)
      rw [autLin_coe, permute_apply_self] at this
      rw [autLin_coe]
      exact this
    have h2 := hsyn (autLin g⁻¹ x) hx0
    rw [formAct_apply, autLin_inv_apply] at h2
    rw [← h2, indicator_map]
    conv_lhs => rw [← autLin_inv_apply g x, autLin_coe]
    rw [dotProduct_permute]

/-! ## Lemma 6.3 for the order-2 search -/

/-- The solutions of the order-2 search: forms of the slice `S_0 = A_0 ∩ slice` that are not ruled out. -/
def IsSol (k : Fin 41) {m : ℕ} (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m)
    (B : LinearMap.BilinForm (ZMod 2) (Yc k)) : Prop :=
  InA0 (Yc k) (allOnes_mem_Yc k) B ∧ B ∈ slice E ∧ ¬ RuledOut (Yc k) B

/-- **Lemma 6.3 for `Y_k`.** If the search removes a node only when every extension violates a constraint or when some
`g ∈ Aut(Y_k)` has `K(B^g) < K(B)` for every extension `B` (for a key `K` constant on the cosets of `G_0`), then a solution
exists only if one has no removed node on its path, i.e. only if the search reports one. -/
theorem lemma63_order2 (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) {N κ : Type*} [LinearOrder κ]
    [WellFoundedLT κ] (ext : LinearMap.BilinForm (ZMod 2) (Yc k) → N → Prop) (removed : N → Prop)
    (K : LinearMap.BilinForm (ZMod 2) (Yc k) → κ) (hK : ∀ B, ∀ D ∈ G0 (Yc k), K (B + D) = K B)
    (hrem : ∀ n, removed n → (∀ B, ext B n → ¬ IsSol k E B) ∨
      ∃ g : Aut (Yc k), ∀ B, ext B n → K (formAct g B) < K B)
    (hex : ∃ B, IsSol k E B) : ∃ B, IsSol k E B ∧ ∀ n, ext B n → ¬ removed n := by
  refine lemma63_abstract ext (IsSol k E) removed formAct K (sliceRep E) ?_ ?_ hrem hex
  · rintro g B ⟨hA, -, hnr⟩
    have hD := sliceRep_sub_mem E (formAct g B)
    have hrep : formAct g B + (sliceRep E (formAct g B) - formAct g B) = sliceRep E (formAct g B) := by abel
    refine ⟨?_, sliceRep_mem_slice E _, ?_⟩
    · rw [← hrep]
      exact InA0_add (InA0_formAct hA g) hD
    · rw [← hrep, ruledOut_add_iff _ hD]
      exact fun h => hnr (ruledOut_of_ruledOut_formAct g h)
  · intro g B
    have hD := sliceRep_sub_mem E (formAct g B)
    have hrep : formAct g B + (sliceRep E (formAct g B) - formAct g B) = sliceRep E (formAct g B) := by abel
    rw [← hrep, hK _ _ hD]

/-! ## The program's tests: keys, syndromes and the coset rule -/

/-- The syndrome of `B` at `w` against words `xs` (for the program, a basis of `Y_w`): `s_w(B)_j = B(w, xs j)`. -/
def syn {m : ℕ} (B : LinearMap.BilinForm (ZMod 2) Y) (w : Y) (xs : Fin m → Y) : Fin m → ZMod 2 :=
  fun j => B w (xs j)

/-- Syndromes against words disjoint from `w` are constant on the cosets of `G_0` (Lemma 6.1 (b)). -/
theorem syn_add {m : ℕ} (B : LinearMap.BilinForm (ZMod 2) Y) {D : LinearMap.BilinForm (ZMod 2) Y}
    (hD : D ∈ G0 Y) (w : Y) (xs : Fin m → Y)
    (hxs : ∀ j i, (w : ι → ZMod 2) i = 0 ∨ (xs j : ι → ZMod 2) i = 0) : syn (B + D) w xs = syn B w xs := by
  funext j
  simp only [syn, LinearMap.add_apply, G0_apply_disjoint D hD w (xs j) (hxs j), add_zero]

/-- `s_w(B^g) = T s_{w g}(B)`, where `T` expresses the words `xs j · g` in the words `xs'`: this is the matrix
`T_{g,w}` of Section 6.2. For `σ` fixing `w` it gives `s_w(B^σ) = T_σ s_w(B)`. -/
theorem syn_formAct {m m' : ℕ} (B : LinearMap.BilinForm (ZMod 2) Y) (g : Aut Y) (w : Y) (xs : Fin m → Y)
    (xs' : Fin m' → Y) (T : Matrix (Fin m) (Fin m') (ZMod 2)) (hT : ∀ j, autLin g (xs j) = ∑ l, T j l • xs' l) :
    syn (formAct g B) w xs = T.mulVec (syn B (autLin g w) xs') := by
  funext j
  simp only [syn, formAct_apply, hT j, map_sum, map_smul, Matrix.mulVec, dotProduct, smul_eq_mul]

/-- Keys are tuples of syndromes (read as numbers) compared lexicographically; a smaller first component gives a
smaller key. -/
theorem key_lt_of_head_lt {r : ℕ} (a b : Fin (r + 1) → ℕ) (h : a 0 < b 0) : toLex a < toLex b :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩

/-- The second test: if the leading bits (above position `t`) of `a` are smaller than those of `b`, then `a < b`,
whatever the lower bits are. -/
theorem lt_of_leading_bits_lt (a b t : ℕ) (h : a / 2 ^ t < b / 2 ^ t) : a < b :=
  Nat.lt_of_div_lt_div h

/-- The first test compares the components of two keys in order: if they agree before position `j` and the `j`-th
component of `a` is smaller, then `a < b`. -/
theorem key_lt_of_first_diff {r : ℕ} (a b : Fin r → ℕ) (j : Fin r) (heq : ∀ i < j, a i = b i) (hlt : a j < b j) :
    toLex a < toLex b :=
  ⟨j, heq, hlt⟩

/-- The key of Section 6.2: the syndromes of the key words `ks i` against the words `xss i` (for the program, bases of
the spaces `Y_{ks i}`), each read as a number by `rd i`, compared lexicographically. -/
def key {r : ℕ} {ms : Fin r → ℕ} (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ) (ks : Fin r → Y)
    (xss : ∀ i, Fin (ms i) → Y) (B : LinearMap.BilinForm (ZMod 2) Y) : Lex (Fin r → ℕ) :=
  toLex fun i => rd i (syn B (ks i) (xss i))

/-- The key depends only on the coset `B + G_0` when the words `xss i` are disjoint from `ks i` (Lemma 6.1 (b)). -/
theorem key_add {r : ℕ} {ms : Fin r → ℕ} (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ) (ks : Fin r → Y)
    (xss : ∀ i, Fin (ms i) → Y) (hdisj : ∀ i j l, (ks i : ι → ZMod 2) l = 0 ∨ (xss i j : ι → ZMod 2) l = 0)
    (B : LinearMap.BilinForm (ZMod 2) Y) {D : LinearMap.BilinForm (ZMod 2) Y} (hD : D ∈ G0 Y) :
    key rd ks xss (B + D) = key rd ks xss B := by
  unfold key
  congr 1
  funext i
  rw [syn_add B hD (ks i) (xss i) (hdisj i)]

/-- **Lemma 6.3 for `Y_k` with the key of Section 6.2.** -/
theorem lemma63_key (k : Fin 41) {m : ℕ}
    (E : EchelonBasis (V := LinearMap.BilinForm (ZMod 2) (Yc k)) (G0 (Yc k)) m) {r : ℕ} {ms : Fin r → ℕ}
    (rd : ∀ i, (Fin (ms i) → ZMod 2) → ℕ) (ks : Fin r → Yc k) (xss : ∀ i, Fin (ms i) → Yc k)
    (hdisj : ∀ i j l, (ks i : Fin 36 → ZMod 2) l = 0 ∨ (xss i j : Fin 36 → ZMod 2) l = 0)
    {N : Type*} (ext : LinearMap.BilinForm (ZMod 2) (Yc k) → N → Prop) (removed : N → Prop)
    (hrem : ∀ n, removed n → (∀ B, ext B n → ¬ IsSol k E B) ∨
      ∃ g : Aut (Yc k), ∀ B, ext B n → key rd ks xss (formAct g B) < key rd ks xss B)
    (hex : ∃ B, IsSol k E B) : ∃ B, IsSol k E B ∧ ∀ n, ext B n → ¬ removed n :=
  lemma63_order2 k E ext removed (key rd ks xss) (fun B _ hD => key_add rd ks xss hdisj B hD) hrem hex

/-- **The first test.** If for every extension `B` of a node the keys of `B^g` and `B` agree before position `j` and the
`j`-th component of the key of `B^g` is smaller, the node satisfies the removal condition of Lemma 6.3 with `g`. -/
theorem first_test {F N Γ : Type*} {r : ℕ} (ext : F → N → Prop) (n : N) (act : Γ → F → F) (K : F → Fin r → ℕ)
    (g : Γ) (j : Fin r) (heq : ∀ B, ext B n → ∀ i < j, K (act g B) i = K B i)
    (hlt : ∀ B, ext B n → K (act g B) j < K B j) : ∀ B, ext B n → toLex (K (act g B)) < toLex (K B) :=
  fun B hB => key_lt_of_first_diff _ _ j (heq B hB) (hlt B hB)

/-- **The coset rule** (first component of the first test). Let `H` be a finite set of group elements (for the program a
coset `Γ₀ g`) with table values `c h`. If every extension `B` of a node has first key component `s₀`, the key of `B^h` has
first component `c h` for each `h ∈ H`, and the smallest table value is below `s₀`, then one `h ∈ H` has `K(B^h) < K(B)`
for every extension `B`. -/
theorem coset_rule {F N Γ : Type*} {r : ℕ} (ext : F → N → Prop) (n : N) (act : Γ → F → F) (K : F → Fin (r + 1) → ℕ)
    (H : Finset Γ) (hH : H.Nonempty) (c : Γ → ℕ) (s₀ : ℕ) (hc : ∀ h ∈ H, ∀ B, ext B n → K (act h B) 0 = c h)
    (hs₀ : ∀ B, ext B n → K B 0 = s₀) (hmin : H.inf' hH c < s₀) :
    ∃ h ∈ H, ∀ B, ext B n → toLex (K (act h B)) < toLex (K B) := by
  obtain ⟨h, hh, heq⟩ := Finset.exists_mem_eq_inf' hH c
  refine ⟨h, hh, fun B hB => key_lt_of_head_lt _ _ ?_⟩
  rw [hc h hh B hB, hs₀ B hB, ← heq]
  exact hmin

/-- **The second test.** If for every extension `B` of a node the bits above position `t` of the first key components of
`B^g` and of `B` are `a` and `b`, and `a < b`, then `K(B^g) < K(B)` for every extension `B`. -/
theorem second_test {F N Γ : Type*} {r : ℕ} (ext : F → N → Prop) (n : N) (act : Γ → F → F) (K : F → Fin (r + 1) → ℕ)
    (g : Γ) (t a b : ℕ) (ha : ∀ B, ext B n → K (act g B) 0 / 2 ^ t = a) (hb : ∀ B, ext B n → K B 0 / 2 ^ t = b)
    (hab : a < b) : ∀ B, ext B n → toLex (K (act g B)) < toLex (K B) :=
  fun B hB => key_lt_of_head_lt _ _ (lt_of_leading_bits_lt _ _ t (by rw [ha B hB, hb B hB]; exact hab))

end C72.T6
