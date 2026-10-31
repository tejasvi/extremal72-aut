import C72T2.TheoremB

/-!
# T6 (order 3): Proposition 4.3, converse direction, and its class invariance

**Proposition 4.3.** A doubly-even self-dual `[72,36,16]` code with an automorphism of order 3 exists if and only
if some Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid Golay code on its coordinates. Whether such a
Golay code exists depends only on the class of the code under monomial equivalence and conjugation.

* `prop43_converse`: if `E` is Hermitian self-dual with minimum weight 8 and `π(G24)` is valid for `E`, then
  `C = {g^{(3)} : g ∈ π(G24)} ⊕ φ(E)` is a doubly-even self-dual `[72,36,16]` code (`Ext72`) with `σ ∈ Aut C` of
  order 3. Self-duality is proved without counting dimensions: a word `v ⊥ C` splits as
  `e₀(v) + (v + e₀(v)) = g^{(3)} + φ(e)`, and `g ∈ G^⊥ = G`, `e ∈ E^{⊥_H} = E`.
* `prop43`: the equivalence, with T2's `prop43_forward` (from `H_CP3`, `H_Golay`, `H_LP`) for the forward
  direction.
* Class invariance (`exists_validGolay_iff`): monomial equivalence (`MonEquiv`, a permutation of the coordinates
  followed by nonzero scalars) and conjugation (`conjCode`) move supports by a permutation (`SuppEquiv`), and a
  valid Golay code `π(G24)` for `E` gives the valid Golay code `pπ(G24)` for the image (`validGolay_of_suppEquiv`).
-/

namespace C72.Three

open Equiv Finset F4

/-! ## Valid Golay codes give (W8), (W10), (W12) -/

theorem exists_of_mem_map_G24 {π : Perm (Fin 24)} {g : Fin 24 → ZMod 2}
    (hg : g ∈ G24.map (permute π).toLinearMap) : ∃ x ∈ G24, permute π x = g := by
  obtain ⟨x, hx, hxg⟩ := Submodule.mem_map.1 hg
  exact ⟨x, hx, hxg⟩

theorem W_of_validGolay {E : Submodule F4 (Fin 24 → F4)} {π : Perm (Fin 24)} (hv : ValidGolay E π) :
    W8 (G24.map (permute π).toLinearMap) E ∧ W10 (G24.map (permute π).toLinearMap) E ∧
      W12 (G24.map (permute π).toLinearMap) E := by
  refine ⟨fun g hg hg8 e he he8 => ?_, fun g hg hg8 e he he10 hsub => ?_,
    fun g hg hg12 e he he12 heq => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_G24 hg
    rw [wt_permute] at hg8
    by_contra hcon
    refine hv.1 (supp x) ⟨x, hx, hg8, rfl⟩ ⟨e, he, Or.inl ⟨he8, ?_⟩⟩
    rw [← supp_permute]
    omega
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_G24 hg
    rw [wt_permute] at hg8
    refine hv.1 (supp x) ⟨x, hx, hg8, rfl⟩ ⟨e, he, Or.inr ⟨he10, ?_⟩⟩
    rw [← supp_permute]
    exact hsub
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_G24 hg
    rw [wt_permute] at hg12
    refine hv.2 (supp x) ⟨x, hx, hg12, rfl⟩ ⟨e, he, he12, ?_⟩
    rw [← supp_permute]
    exact heq

/-! ## The converse direction -/

/-- `Tr(z) = Tr(ω̄ z) = 0` only for `z = 0`. -/
theorem eq_zero_of_tr_wb : ∀ z : F4, tr z = 0 → tr (F4.wb * z) = 0 → z = 0 := by
  decide

/-- **Proposition 4.3, converse direction.** If a Hermitian self-dual code `E` of length 24 over `𝔽₄` with minimum
weight 8 has a valid Golay code `π(G24)` on its coordinates, then `C = {g^{(3)} : g ∈ π(G24)} ⊕ φ(E)` is a
doubly-even self-dual `[72,36,16]` code, and `σ` is an automorphism of `C` of order 3. -/
theorem prop43_converse {E : Submodule F4 (Fin 24 → F4)} (hE : HSelfDual E)
    (hE8 : ∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) (hEw : ∃ e ∈ E, wt e = 8) {π : Perm (Fin 24)}
    (hv : ValidGolay E π) :
    Ext72 (Cof (G24.map (permute π).toLinearMap) E) ∧
      sigma3 ∈ Aut (Cof (G24.map (permute π).toLinearMap) E) ∧ orderOf sigma3 = 3 := by
  set G := G24.map (permute π).toLinearMap with hGdef
  have hG : SelfDual G := G24_selfDual.map_permute π
  have hG4 : ∀ g ∈ G, 4 ∣ wt g := (G24_typeII.map_permute π).2
  have hEle : E ≤ hdual E := le_of_eq hE
  have htrip : ∀ g ∈ G, triple g ∈ Cof G E := fun g hg =>
    ⟨g, hg, 0, E.zero_mem, by rw [phi_zero, add_zero]⟩
  have hphi : ∀ e ∈ E, phi e ∈ Cof G E := fun e he =>
    ⟨0, G.zero_mem, e, he, by rw [map_zero, zero_add]⟩
  -- self-orthogonal
  have hle : Cof G E ≤ dual (Cof G E) := by
    rintro _ ⟨g, hg, e, he, rfl⟩
    rw [mem_dual]
    rintro _ ⟨g', hg', e', he', rfl⟩
    have hgg : g ⬝ᵥ g' = 0 := by
      have hgd : g ∈ dual G := by rw [← hG]; exact hg
      exact hgd g' hg'
    have hee : hform e e' = 0 := hEle he e' he'
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_triple, dotProduct_triple_phi,
      dotProduct_comm (phi e) (triple g'), dotProduct_triple_phi, dotProduct_phi, hgg, hee, tr_zero]
    simp
  -- every word orthogonal to `C` lies in `C`
  have hge : dual (Cof G E) ≤ Cof G E := by
    intro v hv
    rw [mem_dual] at hv
    have hp : (orderOf sigma3).Prime := by
      rw [orderOf_sigma3]
      exact Nat.prime_three
    have hodd : Odd (orderOf sigma3) := by
      rw [orderOf_sigma3]
      decide
    set y := e0 sigma3 v with hydef
    have hyfix : ∀ i, y (sigma3 i) = y i := fun i => e0_apply_apply sigma3 v i
    have hz0 : e0 sigma3 (v + y) = 0 := by
      rw [map_add, hydef, e0_e0 sigma3 hodd, vec_add_self]
    have hzc : ∀ k, (v + y) (idx k 0) + (v + y) (idx k 1) + (v + y) (idx k 2) = 0 := fun k => by
      rw [← e0_sigma3_idx, hz0]
      rfl
    set gv : Fin 24 → ZMod 2 := fun k => y (idx k 0) with hgv
    set ev : Fin 24 → F4 := fun k => psiInv (fun b => (v + y) (idx k b)) with hev
    have htg : triple gv = y := fixed_eq_triple hyfix
    have hpe : phi ev = v + y := even_eq_phi hzc
    have hsplit : triple gv + phi ev = v := by
      rw [htg, hpe, ← add_assoc, add_comm y v, add_assoc, vec_add_self, add_zero]
    have hgvG : gv ∈ G := by
      rw [hG, mem_dual]
      intro g hg
      have h1 := hv _ (htrip g hg)
      rw [← hsplit, add_dotProduct, dotProduct_comm (phi ev) (triple g), dotProduct_triple_phi, add_zero,
        dotProduct_triple] at h1
      exact h1
    have hevE : ev ∈ E := by
      rw [hE, mem_hdual]
      intro e he
      have h1 := hv _ (hphi e he)
      have h2 := hv _ (hphi _ (E.smul_mem F4.w he))
      rw [← hsplit, add_dotProduct, dotProduct_triple_phi, zero_add, dotProduct_phi] at h1 h2
      rw [hform_smul_right] at h2
      exact eq_zero_of_tr_wb _ h1 h2
    rw [← hsplit]
    exact ⟨gv, hgvG, ev, hevE, rfl⟩
  have hsd : SelfDual (Cof G E) := le_antisymm hle hge
  -- doubly-even
  have hde : ∀ c ∈ Cof G E, 4 ∣ wt c := by
    rintro _ ⟨g, hg, e, he, rfl⟩
    have h41 := lemma41 g e
    have h4 := hG4 g hg
    obtain ⟨r, hr⟩ := hE.even_wt he
    omega
  -- minimum weight 16, by Lemma 4.2
  have hmin : MinWt (Cof G E) 16 := by
    obtain ⟨h8, h10, h12⟩ := W_of_validGolay hv
    exact lemma42_converse ⟨π, rfl⟩ hE hE8 h8 h10 h12
  -- a word of weight 16: `φ(e)` for a word `e` of weight 8
  have hw16 : ∃ c ∈ Cof G E, wt c = 16 := by
    obtain ⟨e, he, he8⟩ := hEw
    exact ⟨phi e, hphi e he, by rw [wt_phi, he8]⟩
  -- `σ ∈ Aut C`
  have hσ : sigma3 ∈ Aut (Cof G E) := by
    apply mem_Aut_of_map_le
    rintro _ ⟨c, ⟨g, hg, e, he, rfl⟩, rfl⟩
    show permute sigma3 (triple g + phi e) ∈ Cof G E
    rw [map_add, permute_sigma3_triple, permute_sigma3_phi]
    exact ⟨g, hg, F4.w • e, E.smul_mem F4.w he, rfl⟩
  exact ⟨⟨⟨hsd, hde⟩, hmin, hw16⟩, hσ, orderOf_sigma3⟩

/-- **Proposition 4.3** (first sentence), from the named hypotheses of the forward direction. -/
theorem prop43 (hCP3 : H_CP3) (hGolay : H_Golay) (hLP : H_LP) :
    (∃ C : Code 72, Ext72 C ∧ ∃ g ∈ Aut C, orderOf g = 3) ↔
      ∃ E : Submodule F4 (Fin 24 → F4), HSelfDual E ∧ (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) ∧
        (∃ e ∈ E, wt e = 8) ∧ ∃ π : Perm (Fin 24), ValidGolay E π := by
  constructor
  · rintro ⟨C, hC, g, hg, h3⟩
    exact prop43_forward hCP3 hGolay hLP hC hg h3
  · rintro ⟨E, hE, hE8, hEw, π, hv⟩
    obtain ⟨hext, hσ, h3⟩ := prop43_converse hE hE8 hEw hv
    exact ⟨_, hext, sigma3, hσ, h3⟩

/-! ## Class invariance -/

/-- `E'` has the same weights and supports as `E`, moved by the permutation `p` of the coordinates. -/
def SuppEquiv (p : Perm (Fin 24)) (E E' : Submodule F4 (Fin 24 → F4)) : Prop :=
  ∀ (w : ℕ) (s : Finset (Fin 24)),
    (∃ e ∈ E, wt e = w ∧ supp e = s) ↔ ∃ e' ∈ E', wt e' = w ∧ supp e' = s.map p.toEmbedding

theorem map_map_symm (p : Perm (Fin 24)) (s : Finset (Fin 24)) :
    (s.map p.symm.toEmbedding).map p.toEmbedding = s := by
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hy
    exact ⟨p.symm y, ⟨y, hy, rfl⟩, by simp⟩

theorem SuppEquiv.symm {p : Perm (Fin 24)} {E E' : Submodule F4 (Fin 24 → F4)} (h : SuppEquiv p E E') :
    SuppEquiv p⁻¹ E' E := by
  intro w s
  have := h w (s.map p⁻¹.toEmbedding)
  rw [show (s.map p⁻¹.toEmbedding).map p.toEmbedding = s from map_map_symm p s] at this
  exact this.symm

theorem SuppEquiv.trans {p q : Perm (Fin 24)} {E E' E'' : Submodule F4 (Fin 24 → F4)}
    (h : SuppEquiv p E E') (h' : SuppEquiv q E' E'') : SuppEquiv (q * p) E E'' := by
  intro w s
  rw [h w s, h' w (s.map p.toEmbedding), Finset.map_map]
  rfl

/-- A valid Golay code moves with the supports: if `π(G24)` is valid for `E`, then `pπ(G24)` is valid for `E'`. -/
theorem validGolay_of_suppEquiv {p : Perm (Fin 24)} {E E' : Submodule F4 (Fin 24 → F4)}
    (hp : SuppEquiv p E E') {π : Perm (Fin 24)} (hv : ValidGolay E π) : ValidGolay E' (p * π) := by
  have himg : ∀ O : Finset (Fin 24), O.map (p * π).toEmbedding = (O.map π.toEmbedding).map p.toEmbedding :=
    fun O => by rw [Finset.map_map]; rfl
  -- the word `e'` of `E'` comes from a word `e` of `E` with support `p⁻¹(supp e')`
  have hback : ∀ e' ∈ E', ∃ e ∈ E, wt e = wt e' ∧ (supp e).map p.toEmbedding = supp e' := by
    intro e' he'
    obtain ⟨e, he, hw, hs⟩ := (hp (wt e') ((supp e').map p.symm.toEmbedding)).2
      ⟨e', he', rfl, (map_map_symm p (supp e')).symm⟩
    exact ⟨e, he, hw, by rw [hs, map_map_symm]⟩
  refine ⟨fun O hO hf => ?_, fun D hD hf => ?_⟩
  · obtain ⟨e', he', hcase⟩ := hf
    obtain ⟨e, he, hw, hs⟩ := hback e' he'
    rw [himg, ← hs, ← Finset.map_inter, Finset.card_map, Finset.map_subset_map] at hcase
    exact hv.1 O hO ⟨e, he, by rw [hw]; exact hcase⟩
  · obtain ⟨e', he', hw12, hs12⟩ := hf
    obtain ⟨e, he, hw, hs⟩ := hback e' he'
    rw [himg, ← hs] at hs12
    exact hv.2 D hD ⟨e, he, by rw [hw, hw12], Finset.map_injective p.toEmbedding hs12⟩

/-- The monomial map: the permutation `p` of the coordinates followed by multiplication by the scalars `d`,
`x ↦ (dᵢ x_{p⁻¹(i)})ᵢ`. -/
def monomial (p : Perm (Fin 24)) (d : Fin 24 → F4) : (Fin 24 → F4) →ₗ[F4] (Fin 24 → F4) where
  toFun x i := d i * x (p.symm i)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, mul_add]
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- `E'` is monomially equivalent to `E`. -/
def MonEquiv (E E' : Submodule F4 (Fin 24 → F4)) : Prop :=
  ∃ (p : Perm (Fin 24)) (d : Fin 24 → F4), (∀ i, d i ≠ 0) ∧ E.map (monomial p d) = E'

/-- The conjugate code `{x̄ | x ∈ E}`, `x̄ᵢ = xᵢ²`. -/
def conjCode (E : Submodule F4 (Fin 24 → F4)) : Submodule F4 (Fin 24 → F4) where
  carrier := {x | (fun i => star (x i)) ∈ E}
  add_mem' := by
    intro x y hx hy
    have h := E.add_mem hx hy
    simp only [Set.mem_ofPred_eq, Pi.add_apply, F4.star_add] at h ⊢
    exact h
  zero_mem' := by
    show (fun i => star ((0 : Fin 24 → F4) i)) ∈ E
    simp only [Pi.zero_apply, F4.star_zero]
    exact E.zero_mem
  smul_mem' := by
    intro a x hx
    have h := E.smul_mem (star a) hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, F4.star_mul] at h ⊢
    exact h

/-- The classes of Theorem C: monomial equivalence, after conjugation if needed. -/
def MonConjEquiv (E E' : Submodule F4 (Fin 24 → F4)) : Prop :=
  MonEquiv E E' ∨ MonEquiv (conjCode E) E'

theorem supp_monomial {p : Perm (Fin 24)} {d : Fin 24 → F4} (hd : ∀ i, d i ≠ 0) (x : Fin 24 → F4) :
    supp (monomial p d x) = (supp x).map p.toEmbedding := by
  ext i
  rw [mem_supp, Finset.mem_map]
  show d i * x (p.symm i) ≠ 0 ↔ ∃ a ∈ supp x, p.toEmbedding a = i
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨p.symm i, mem_supp.2 h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hd _, by simpa using mem_supp.1 hw⟩

theorem suppEquiv_monomial {p : Perm (Fin 24)} {d : Fin 24 → F4} (hd : ∀ i, d i ≠ 0)
    (E : Submodule F4 (Fin 24 → F4)) : SuppEquiv p E (E.map (monomial p d)) := by
  intro w s
  constructor
  · rintro ⟨e, he, hw, rfl⟩
    refine ⟨monomial p d e, Submodule.mem_map_of_mem he, ?_, supp_monomial hd e⟩
    rw [← card_supp, supp_monomial hd, Finset.card_map, card_supp, hw]
  · rintro ⟨_, ⟨e, he, rfl⟩, hw, hs⟩
    refine ⟨e, he, ?_, ?_⟩
    · rw [← hw, ← card_supp, ← card_supp, supp_monomial hd, Finset.card_map]
    · rw [supp_monomial hd] at hs
      exact Finset.map_injective p.toEmbedding hs

theorem supp_star (x : Fin 24 → F4) : supp (fun i => star (x i)) = supp x := by
  ext i
  simp only [mem_supp]
  have key : ∀ a : F4, star a ≠ 0 ↔ a ≠ 0 := by decide
  exact key (x i)

theorem suppEquiv_conj (E : Submodule F4 (Fin 24 → F4)) : SuppEquiv 1 E (conjCode E) := by
  intro w s
  have hs1 : s.map (1 : Perm (Fin 24)).toEmbedding = s := by
    exact Finset.map_refl
  rw [hs1]
  constructor
  · rintro ⟨e, he, hw, rfl⟩
    refine ⟨fun i => star (e i), ?_, ?_, supp_star e⟩
    · show (fun i => star (star (e i))) ∈ E
      simp only [F4.star_star]
      exact he
    · rw [← card_supp, supp_star, card_supp, hw]
  · rintro ⟨e', he', hw, rfl⟩
    refine ⟨fun i => star (e' i), he', ?_, supp_star e'⟩
    rw [← card_supp, supp_star, card_supp, hw]

theorem suppEquiv_of_monConjEquiv {E E' : Submodule F4 (Fin 24 → F4)} (h : MonConjEquiv E E') :
    ∃ p : Perm (Fin 24), SuppEquiv p E E' := by
  rcases h with ⟨p, d, hd, rfl⟩ | ⟨p, d, hd, rfl⟩
  · exact ⟨p, suppEquiv_monomial hd E⟩
  · exact ⟨p * 1, (suppEquiv_conj E).trans (suppEquiv_monomial hd _)⟩

/-- **Proposition 4.3** (second sentence): whether a valid Golay code exists depends only on the class of the
code under monomial equivalence and conjugation. -/
theorem exists_validGolay_iff {E E' : Submodule F4 (Fin 24 → F4)} (h : MonConjEquiv E E') :
    (∃ π : Perm (Fin 24), ValidGolay E π) ↔ ∃ π : Perm (Fin 24), ValidGolay E' π := by
  obtain ⟨p, hp⟩ := suppEquiv_of_monConjEquiv h
  constructor
  · rintro ⟨π, hv⟩
    exact ⟨p * π, validGolay_of_suppEquiv hp hv⟩
  · rintro ⟨π, hv⟩
    exact ⟨p⁻¹ * π, validGolay_of_suppEquiv hp.symm hv⟩

end C72.Three
