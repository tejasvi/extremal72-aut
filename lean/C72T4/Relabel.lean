import C72T4.Hyps

/-!
# T4: relabelling a code with a fixed-point-free involution to the pair model

Let `a` be a fixed-point-free involution of a finite set of coordinates `ι`. Every orbit of `a` is `{j, a j}`
(`sameCycle_involution`); there are `card ι / 2` orbits (`two_mul_card_orbits`). Given a bijection `ψ` from the orbits
to an index type `κ`, `pairEquiv` numbers the coordinates as pairs `(ψ ω, e)`, `e = 0` at a chosen element of the orbit
`ω`. Then `a` becomes `aStd : (i, e) ↦ (i, e + 1)` (`pairEquiv_apply_apply`), and for a code `C` invariant under `a` the
relabelled code `C'` has `aStd` as an automorphism and contracted fixed code `Yof C' = (contracted a C)` moved by `ψ`
(`Yof_map_pairEquiv`).
-/

namespace C72.T4

open C72 Module Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : Perm ι}

omit [Fintype ι] [DecidableEq ι] in
theorem pow_apply_involution (ha2 : a * a = 1) (j : ι) : ∀ n : ℕ, (a ^ n) j = j ∨ (a ^ n) j = a j
  | 0 => Or.inl rfl
  | n + 1 => by
    rcases pow_apply_involution ha2 j n with h | h
    · right
      rw [pow_succ', Perm.mul_apply, h]
    · left
      rw [pow_succ', Perm.mul_apply, h, ← Perm.mul_apply, ha2, Perm.one_apply]

omit [DecidableEq ι] in
/-- For an involution `a`, the orbit of `j` is `{j, a j}`. -/
theorem sameCycle_involution (ha2 : a * a = 1) {j j' : ι} (h : a.SameCycle j j') : j' = j ∨ j' = a j := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact pow_apply_involution ha2 j n

omit [Fintype ι] [DecidableEq ι] in
theorem involution_apply_apply (ha2 : a * a = 1) (j : ι) : a (a j) = j := by
  rw [← Perm.mul_apply, ha2, Perm.one_apply]

/-- A chosen element of each orbit. -/
noncomputable def rep (ω : Orbits a) : ι :=
  Quotient.out (s := Equiv.Perm.SameCycle.setoid a) ω

omit [Fintype ι] [DecidableEq ι] in
theorem toOrbit_rep (ω : Orbits a) : toOrbit a (rep ω) = ω :=
  Quotient.out_eq (s := Equiv.Perm.SameCycle.setoid a) ω

omit [DecidableEq ι] in
theorem eq_rep_or (ha2 : a * a = 1) (j : ι) : j = rep (toOrbit a j) ∨ j = a (rep (toOrbit a j)) := by
  have h : toOrbit a (rep (toOrbit a j)) = toOrbit a j := toOrbit_rep _
  rw [toOrbit_eq_toOrbit] at h
  exact sameCycle_involution ha2 h

/-- The relabelling `j ↦ (ψ ω, e)`, `ω` the orbit of `j`, `e = 0` iff `j` is the chosen element of `ω`. -/
noncomputable def pairEquiv {κ : Type*} (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) (ψ : Orbits a ≃ κ) :
    ι ≃ κ × ZMod 2 where
  toFun j := (ψ (toOrbit a j), if j = rep (toOrbit a j) then 0 else 1)
  invFun p := if p.2 = 0 then rep (ψ.symm p.1) else a (rep (ψ.symm p.1))
  left_inv j := by
    show (if (if j = rep (toOrbit a j) then (0 : ZMod 2) else 1) = 0 then rep (ψ.symm (ψ (toOrbit a j)))
      else a (rep (ψ.symm (ψ (toOrbit a j))))) = j
    rw [Equiv.symm_apply_apply]
    by_cases h : j = rep (toOrbit a j)
    · rw [ite_eq_left h, ite_eq_left rfl]
      exact h.symm
    · have h' : j = a (rep (toOrbit a j)) := (eq_rep_or ha2 j).resolve_left h
      rw [ite_eq_right h, ite_eq_right (by decide : (1 : ZMod 2) ≠ 0)]
      exact h'.symm
  right_inv p := by
    obtain ⟨i, e⟩ := p
    rcases zmod2_cases e with rfl | rfl
    · show (ψ (toOrbit a (if (0 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i)))),
        if (if (0 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i))) =
          rep (toOrbit a (if (0 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i)))) then 0 else 1) = (i, 0)
      rw [ite_eq_left rfl, toOrbit_rep, Equiv.apply_symm_apply, ite_eq_left rfl]
    · show (ψ (toOrbit a (if (1 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i)))),
        if (if (1 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i))) =
          rep (toOrbit a (if (1 : ZMod 2) = 0 then rep (ψ.symm i) else a (rep (ψ.symm i)))) then 0 else 1) = (i, 1)
      rw [ite_eq_right (by decide : (1 : ZMod 2) ≠ 0), toOrbit_apply, toOrbit_rep, Equiv.apply_symm_apply,
        ite_eq_right (hfp _)]

theorem pairEquiv_apply {κ : Type*} (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) (ψ : Orbits a ≃ κ) (j : ι) :
    pairEquiv ha2 hfp ψ j = (ψ (toOrbit a j), if j = rep (toOrbit a j) then 0 else 1) :=
  rfl

/-- In the new labels `a` is `aStd`: `Φ (a j) = aStd (Φ j)`. -/
theorem pairEquiv_apply_apply {κ : Type*} (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) (ψ : Orbits a ≃ κ)
    (j : ι) : pairEquiv ha2 hfp ψ (a j) = aStd (pairEquiv ha2 hfp ψ j) := by
  rw [pairEquiv_apply, pairEquiv_apply, aStd_apply, toOrbit_apply]
  congr 1
  by_cases h : j = rep (toOrbit a j)
  · have h' : a j ≠ rep (toOrbit a j) := by
      intro h''
      rw [← h] at h''
      exact hfp j h''
    rw [ite_eq_right h', ite_eq_left h]
    decide
  · have h' : j = a (rep (toOrbit a j)) := (eq_rep_or ha2 j).resolve_left h
    have h'' : a j = rep (toOrbit a j) := by
      conv_lhs => rw [h']
      exact involution_apply_apply ha2 _
    rw [ite_eq_left h'', ite_eq_right h]
    decide

/-- `permute aStd ∘ reindex Φ = reindex Φ ∘ permute a`. -/
theorem permute_aStd_reindex {κ : Type*} (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) (ψ : Orbits a ≃ κ)
    (c : ι → ZMod 2) :
    permute aStd (reindex (pairEquiv ha2 hfp ψ) c) = reindex (pairEquiv ha2 hfp ψ) (permute a c) := by
  funext p
  simp only [permute_apply, reindex_apply]
  congr 1
  apply (pairEquiv ha2 hfp ψ).injective
  rw [Equiv.apply_symm_apply]
  have h := pairEquiv_apply_apply ha2 hfp ψ (a.symm ((pairEquiv ha2 hfp ψ).symm p))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact (Equiv.symm_apply_eq aStd).2 h

/-- The contracted fixed code of the relabelled code is the contracted fixed code of `a`, moved by `ψ`. -/
theorem Yof_map_pairEquiv {κ : Type*} [Fintype κ] (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i)
    (ψ : Orbits a ≃ κ) (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Yof (C.map (reindex (pairEquiv ha2 hfp ψ)).toLinearMap) = (contracted a C).map (reindex ψ).toLinearMap := by
  ext u
  rw [mem_Yof, mem_map_reindex, mem_map_reindex, mem_contracted]
  have h : reindex (pairEquiv ha2 hfp ψ).symm (pv u u) = expand a (reindex ψ.symm u) := by
    funext j
    simp only [reindex_apply, Equiv.symm_symm, expand_apply, pairEquiv_apply, pv]
    split_ifs <;> rfl
  rw [h]

/-- The orbits of a fixed-point-free involution have two elements each. -/
theorem card_fiber_involution (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) (ω : Orbits a) :
    #(univ.filter (fun j => toOrbit a j = ω)) = 2 := by
  have h : univ.filter (fun j => toOrbit a j = ω) = {rep ω, a (rep ω)} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hj
      have h1 : toOrbit a (rep ω) = toOrbit a j := by rw [toOrbit_rep, hj]
      rw [toOrbit_eq_toOrbit] at h1
      exact sameCycle_involution ha2 h1
    · rintro (rfl | rfl)
      · exact toOrbit_rep ω
      · rw [toOrbit_apply, toOrbit_rep]
  rw [h, Finset.card_pair (fun h' => hfp (rep ω) h'.symm)]

/-- A fixed-point-free involution of `ι` has `card ι / 2` orbits. -/
theorem two_mul_card_orbits (ha2 : a * a = 1) (hfp : ∀ i, a i ≠ i) :
    2 * Fintype.card (Orbits a) = Fintype.card ι := by
  have h := Finset.card_eq_sum_card_fiberwise (f := toOrbit a) (s := univ) (t := univ)
    (fun x _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun ω _ => card_fiber_involution ha2 hfp ω), Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Finset.card_univ] at h
  omega

end C72.T4
