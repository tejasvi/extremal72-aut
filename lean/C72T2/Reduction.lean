import C72T2.Coords

/-!
# T2: the codes `G` and `E` of an automorphism of order 3 (Section 4.1 of the paper)

Let `C` be a binary code of length 72 with `σ = sigma3 ∈ Aut C`, where `σ(k, b) = (k, b + 1)`.

* `Gcode C = {g ∈ 𝔽₂²⁴ | g^{(3)} ∈ C}`, so that `F = {c ∈ C | cσ = c} = {g^{(3)} | g ∈ G}`
  (`mem_Fsub_iff_triple`, with T1's `Fsub`);
* `Ecode C = {e ∈ 𝔽₄²⁴ | φ(a e) ∈ C for all a ∈ 𝔽₄}`, an `𝔽₄`-linear code; since `σ` acts on `φ(e)` as
  multiplication by `ω`, `e ∈ Ecode C ↔ φ(e) ∈ C` (`mem_Ecode_iff`), and `E(σ) = φ(E)` (`mem_Esub_iff_phi`, with
  T1's `Esub`, the words of `C` with even weight on every cycle);
* `C = F ⊕ E(σ)` (T1's `decomposition`) gives `C = {g^{(3)} + φ(e) | g ∈ G, e ∈ E}`
  (`exists_triple_add_phi`, `Cof_Gcode_Ecode`);
* if `C` is self-dual, then `G` is self-dual (`Gcode_selfDual`) and `E` is Hermitian self-dual
  (`Ecode_hselfDual`), by the inner product formulas of `C72T2.Coords`;
* if `C` is Type II with minimum weight 16, then `G` is Type II with minimum weight at least 8 (`3|g| ≥ 16` and
  `4 ∣ 3|g|`), and every nonzero `e ∈ E` has `wt(e) ≥ 8` (`2 wt(e) ≥ 16`).
-/

namespace C72.Three

open Equiv Finset F4

variable {C : Code 72}

/-! ## The codes `G` and `E` -/

/-- `G = {g ∈ 𝔽₂²⁴ | g^{(3)} ∈ C}`: the fixed subcode of `C` is `{g^{(3)} | g ∈ G}`. -/
def Gcode (C : Code 72) : Code 24 :=
  C.comap triple

theorem mem_Gcode {g : Fin 24 → ZMod 2} : g ∈ Gcode C ↔ triple g ∈ C :=
  Iff.rfl

/-- `E = {e ∈ 𝔽₄²⁴ | φ(a e) ∈ C for all a ∈ 𝔽₄}`, an `𝔽₄`-linear code. When `σ ∈ Aut C` it is
`{e | φ(e) ∈ C}` (`mem_Ecode_iff`). -/
def Ecode (C : Code 72) : Submodule F4 (Fin 24 → F4) where
  carrier := {e | ∀ a : F4, phi (a • e) ∈ C}
  zero_mem' := fun a => by
    rw [smul_zero, phi_zero]
    exact C.zero_mem
  add_mem' := fun {x y} hx hy a => by
    rw [smul_add, phi_add]
    exact C.add_mem (hx a) (hy a)
  smul_mem' := fun c x hx a => by
    rw [smul_smul]
    exact hx (a * c)

theorem mem_Ecode_iff (hσ : sigma3 ∈ Aut C) {e : Fin 24 → F4} : e ∈ Ecode C ↔ phi e ∈ C := by
  constructor
  · intro h
    have h1 := h 1
    rwa [one_smul] at h1
  · intro h a
    have hw : phi (F4.w • e) ∈ C := by
      rw [← permute_sigma3_phi]
      exact permute_mem_of_mem_Aut hσ h
    have hwb : phi (F4.wb • e) ∈ C := by
      have h2 : F4.wb • e = F4.w • (F4.w • e) := by
        rw [smul_smul]
        rfl
      rw [h2, ← permute_sigma3_phi]
      exact permute_mem_of_mem_Aut hσ hw
    cases a
    · show phi ((0 : F4) • e) ∈ C
      rw [zero_smul, phi_zero]
      exact C.zero_mem
    · show phi ((1 : F4) • e) ∈ C
      rwa [one_smul]
    · exact hw
    · exact hwb

/-! ## The decomposition `C = {g^{(3)}} ⊕ φ(E)` -/

/-- A word fixed by `σ` is constant on the cycles: it is `g^{(3)}` for `g_k = y(k, 0)`. -/
theorem fixed_eq_triple {y : Fin 72 → ZMod 2} (hy : ∀ i, y (sigma3 i) = y i) :
    triple (fun k => y (idx k 0)) = y := by
  have h1 : ∀ k, y (idx k 1) = y (idx k 0) := fun k => by
    have := hy (idx k 0)
    rwa [sigma3_idx] at this
  have h2 : ∀ k, y (idx k 2) = y (idx k 0) := fun k => by
    have := hy (idx k 1)
    rw [sigma3_idx] at this
    rw [← h1 k]
    exact this
  funext i
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [triple_idx]
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by
    revert b
    decide
  rcases hb with rfl | rfl | rfl
  · rfl
  · exact (h1 k).symm
  · exact (h2 k).symm

/-- A word with even weight on every cycle is `φ(e)`. -/
theorem even_eq_phi {z : Fin 72 → ZMod 2} (hz : ∀ k, z (idx k 0) + z (idx k 1) + z (idx k 2) = 0) :
    phi (fun k => psiInv (fun b => z (idx k b))) = z := by
  funext i
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [phi_idx, psi_psiInv _ (hz k)]

/-- **`C = {g^{(3)} : g ∈ G} ⊕ φ(E)`**: every word of `C` is `g^{(3)} + φ(e)` with `g ∈ G`, `e ∈ E`
([Huf82, Yor83], via T1's `decomposition`). -/
theorem exists_triple_add_phi (hσ : sigma3 ∈ Aut C) {c : Fin 72 → ZMod 2} (hc : c ∈ C) :
    ∃ g ∈ Gcode C, ∃ e ∈ Ecode C, triple g + phi e = c := by
  have hsup := Fsub_sup_Esub (C := C) Nat.prime_three (by norm_num) orderOf_sigma3 hσ
  rw [← hsup] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨hyC, hyfix⟩ := mem_Fsub_iff.1 hy
  have hp : (orderOf sigma3).Prime := by
    rw [orderOf_sigma3]
    exact Nat.prime_three
  have hodd : Odd (orderOf sigma3) := by
    rw [orderOf_sigma3]
    decide
  obtain ⟨hzC, hz0⟩ := (mem_Esub_iff hp hodd).1 hz
  have hzc : ∀ k, z (idx k 0) + z (idx k 1) + z (idx k 2) = 0 := fun k => by
    rw [← e0_sigma3_idx, hz0]
    rfl
  refine ⟨fun k => y (idx k 0), ?_, fun k => psiInv (fun b => z (idx k b)), ?_, ?_⟩
  · rw [mem_Gcode, fixed_eq_triple hyfix]
    exact hyC
  · rw [mem_Ecode_iff hσ, even_eq_phi hzc]
    exact hzC
  · rw [fixed_eq_triple hyfix, even_eq_phi hzc]

/-- `F = {g^{(3)} : g ∈ G}`: the words of `C` fixed by `σ` (T1's `Fsub`) are the words `g^{(3)}`, `g ∈ G`. -/
theorem mem_Fsub_iff_triple {v : Fin 72 → ZMod 2} : v ∈ Fsub C sigma3 ↔ ∃ g ∈ Gcode C, triple g = v := by
  constructor
  · intro hv
    obtain ⟨hvC, hvfix⟩ := mem_Fsub_iff.1 hv
    exact ⟨_, by rw [mem_Gcode, fixed_eq_triple hvfix]; exact hvC, fixed_eq_triple hvfix⟩
  · rintro ⟨g, hg, rfl⟩
    refine mem_Fsub_iff.2 ⟨hg, fun i => ?_⟩
    obtain ⟨k, b, rfl⟩ := exists_idx i
    rw [sigma3_idx, triple_idx, triple_idx]

/-- `E(σ) = φ(E)`: the words of `C` with even weight on every cycle (T1's `Esub`; `σ` has no fixed point) are the
words `φ(e)`, `e ∈ E`. -/
theorem mem_Esub_iff_phi (hσ : sigma3 ∈ Aut C) {v : Fin 72 → ZMod 2} :
    v ∈ Esub C sigma3 ↔ ∃ e ∈ Ecode C, phi e = v := by
  have hp : (orderOf sigma3).Prime := by
    rw [orderOf_sigma3]
    exact Nat.prime_three
  have hodd : Odd (orderOf sigma3) := by
    rw [orderOf_sigma3]
    decide
  rw [mem_Esub_iff hp hodd]
  constructor
  · rintro ⟨hvC, hv0⟩
    have hvc : ∀ k, v (idx k 0) + v (idx k 1) + v (idx k 2) = 0 := fun k => by
      rw [← e0_sigma3_idx, hv0]
      rfl
    refine ⟨_, ?_, even_eq_phi hvc⟩
    rw [mem_Ecode_iff hσ, even_eq_phi hvc]
    exact hvC
  · rintro ⟨e, he, rfl⟩
    refine ⟨(mem_Ecode_iff hσ).1 he, funext fun i => ?_⟩
    obtain ⟨k, b, rfl⟩ := exists_idx i
    rw [e0_sigma3_idx', phi_idx, phi_idx, phi_idx, psi_cycle_sum]
    rfl

/-- The code `{g^{(3)} : g ∈ G} ⊕ φ(E)` built from a binary code `G` of length 24 and an `𝔽₄`-linear code `E`
of length 24 (the code `C` of Lemma 4.2). -/
def Cof (G : Code 24) (E : Submodule F4 (Fin 24 → F4)) : Code 72 where
  carrier := {c | ∃ g ∈ G, ∃ e ∈ E, triple g + phi e = c}
  zero_mem' := ⟨0, G.zero_mem, 0, E.zero_mem, by rw [map_zero, phi_zero, add_zero]⟩
  add_mem' := by
    rintro _ _ ⟨g, hg, e, he, rfl⟩ ⟨g', hg', e', he', rfl⟩
    refine ⟨g + g', G.add_mem hg hg', e + e', E.add_mem he he', ?_⟩
    rw [map_add, phi_add]
    abel
  smul_mem' := by
    rintro a _ ⟨g, hg, e, he, rfl⟩
    rcases zmod2_cases a with rfl | rfl
    · exact ⟨0, G.zero_mem, 0, E.zero_mem, by rw [map_zero, phi_zero, add_zero, zero_smul]⟩
    · exact ⟨g, hg, e, he, by rw [one_smul]⟩

theorem mem_Cof {G : Code 24} {E : Submodule F4 (Fin 24 → F4)} {c : Fin 72 → ZMod 2} :
    c ∈ Cof G E ↔ ∃ g ∈ G, ∃ e ∈ E, triple g + phi e = c :=
  Iff.rfl

/-- `C = {g^{(3)} : g ∈ G} ⊕ φ(E)` for `G = Gcode C` and `E = Ecode C`. -/
theorem Cof_Gcode_Ecode (hσ : sigma3 ∈ Aut C) : Cof (Gcode C) (Ecode C) = C := by
  ext c
  constructor
  · rintro ⟨g, hg, e, he, rfl⟩
    exact C.add_mem hg ((mem_Ecode_iff hσ).1 he)
  · intro hc
    exact exists_triple_add_phi hσ hc

/-! ## Self-duality of `G` and Hermitian self-duality of `E` -/

/-- If `C` is self-dual, so is `G` [Huf82]. -/
theorem Gcode_selfDual (hσ : sigma3 ∈ Aut C) (hC : SelfDual C) : SelfDual (Gcode C) := by
  apply le_antisymm
  · intro g hg
    rw [mem_dual]
    intro g' hg'
    rw [← dotProduct_triple]
    have h : triple g ∈ dual C := by
      rw [← hC]
      exact hg
    exact h _ hg'
  · intro u hu
    rw [mem_Gcode, hC, mem_dual]
    intro c hc
    obtain ⟨g, hg, e, he, rfl⟩ := exists_triple_add_phi hσ hc
    rw [dotProduct_add, dotProduct_triple, dotProduct_triple_phi, add_zero]
    exact hu g hg

/-- If `C` is self-dual, then `E` is Hermitian self-dual [Huf82]: `⟨φ(x), φ(y)⟩ = Tr(⟨x, y⟩_H)`, and a trace form
that vanishes on `⟨x, y⟩_H` and `⟨ω x, y⟩_H` forces `⟨x, y⟩_H = 0`. -/
theorem Ecode_hselfDual (hσ : sigma3 ∈ Aut C) (hC : SelfDual C) : HSelfDual (Ecode C) := by
  apply le_antisymm
  · intro x hx
    rw [mem_hdual]
    intro y hy
    have hyC : phi y ∈ C := (mem_Ecode_iff hσ).1 hy
    have hxC : phi x ∈ dual C := by
      rw [← hC]
      exact (mem_Ecode_iff hσ).1 hx
    have hwx : phi (F4.w • x) ∈ dual C := by
      rw [← hC]
      exact (mem_Ecode_iff hσ).1 ((Ecode C).smul_mem F4.w hx)
    have h1 : tr (hform x y) = 0 := by
      rw [← dotProduct_phi]
      exact hxC _ hyC
    have h2 : tr (F4.w * hform x y) = 0 := by
      rw [← hform_smul_left, ← dotProduct_phi]
      exact hwx _ hyC
    exact eq_zero_of_tr _ h1 h2
  · intro x hx
    rw [mem_Ecode_iff hσ, hC, mem_dual]
    intro c hc
    obtain ⟨g, hg, e, he, rfl⟩ := exists_triple_add_phi hσ hc
    rw [dotProduct_add, dotProduct_comm, dotProduct_triple_phi, zero_add, dotProduct_phi,
      mem_hdual.1 hx e he]
    rfl

/-! ## Weights -/

theorem triple_ne_zero {g : Fin 24 → ZMod 2} (hg : g ≠ 0) : triple g ≠ 0 := by
  intro h
  apply hg
  have h' := congrArg wt h
  rw [wt_triple, wt_zero] at h'
  exact wt_eq_zero.1 (by omega)

theorem phi_ne_zero {e : Fin 24 → F4} (he : e ≠ 0) : phi e ≠ 0 := by
  intro h
  apply he
  have h' := congrArg wt h
  rw [wt_phi, wt_zero] at h'
  exact wt_eq_zero.1 (by omega)

/-- If `C` is Type II, so is `G` (`4 ∣ 3|g|` gives `4 ∣ |g|`). -/
theorem Gcode_typeII (hσ : sigma3 ∈ Aut C) (hC : TypeII C) : TypeII (Gcode C) := by
  refine ⟨Gcode_selfDual hσ hC.1, fun g hg => ?_⟩
  have h := hC.2 _ hg
  rw [wt_triple] at h
  omega

/-- If `C` is doubly-even with minimum weight 16, then `G` has minimum weight at least 8. -/
theorem Gcode_minWt (hC4 : ∀ x ∈ C, 4 ∣ wt x) (hC : MinWt C 16) : MinWt (Gcode C) 8 := by
  intro g hg hne
  have h16 := hC _ hg (triple_ne_zero hne)
  have h4 := hC4 _ hg
  rw [wt_triple] at h16 h4
  omega

/-- If `C` has minimum weight 16, every nonzero word of `E` has weight at least 8 (`|φ(e)| = 2 wt(e)`). -/
theorem Ecode_minWt (hσ : sigma3 ∈ Aut C) (hC : MinWt C 16) : ∀ e ∈ Ecode C, e ≠ 0 → 8 ≤ wt e := by
  intro e he hne
  have h := hC _ ((mem_Ecode_iff hσ).1 he) (phi_ne_zero hne)
  rw [wt_phi] at h
  omega

end C72.Three
