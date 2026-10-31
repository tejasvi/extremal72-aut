import C72T1.Defs
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# T1: the decomposition under an automorphism of odd prime order [Huf82, Yor83]

Let `g` be a permutation of a finite set of coordinates `ι` of prime order `p ≠ 2`, and let `C` be a binary code
with `g ∈ Aut C`. As in the paper (Sections 2.1 and 4.1):

* `cyc g i` is the cycle of `g` through `i` (the orbit of `i` under `⟨g⟩`); it has 1 or `p` elements (`card_cyc`);
* `Fsub C g = {v ∈ C | v g = v}`, the words fixed by `g`;
* `Esub C g` is the set of words of `C` that vanish on the fixed points of `g` and have even weight on each cycle;
* `C = F ⊕ E` (`Fsub_sup_Esub`, `Fsub_inf_Esub`) and `F ⊥ E` (`Fsub_orthogonal_Esub`);
* the contracted fixed code `contracted g C ≤ (Orbits g → 𝔽₂)` keeps one coordinate per orbit, `F = φ₀(C₀)`
  (`Fsub_eq_map_contracted`), and `C₀` is self-dual when `C` is (`contracted_selfDual`).

The proof uses the map `e₀ v = ∑_{k < p} v ∘ g^k`, which is idempotent on binary words because `p` is odd.
-/

namespace C72

open Equiv Equiv.Perm Finset Module

/-! ## Arithmetic in `ZMod 2` -/

theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by
  decide

theorem zmod2_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

theorem vec_add_self {ι : Type*} (v : ι → ZMod 2) : v + v = 0 :=
  funext fun i => zmod2_add_self (v i)

/-- For odd `p`, `p • x = x` in `ZMod 2`. -/
theorem nsmul_odd {p : ℕ} (hp : Odd p) (x : ZMod 2) : p • x = x := by
  rw [nsmul_eq_mul, (ZMod.natCast_eq_one_iff_odd).2 hp, one_mul]

/-- A binary word has even weight on `s` iff its coordinates on `s` sum to `0`. -/
theorem even_card_filter_ne_zero_iff {ι : Type*} (s : Finset ι) (v : ι → ZMod 2) :
    Even #(s.filter (fun j => v j ≠ 0)) ↔ ∑ j ∈ s, v j = 0 := by
  have h : ∑ j ∈ s, v j = (#(s.filter (fun j => v j ≠ 0)) : ZMod 2) := by
    rw [← Finset.sum_filter_ne_zero]
    rw [Finset.sum_congr rfl (fun j hj => zmod2_eq_one_of_ne_zero (v j) (Finset.mem_filter.1 hj).2)]
    rw [Finset.sum_const, nsmul_one]
  rw [h, ZMod.natCast_eq_zero_iff_even]

theorem sum_range_shift_of_periodic {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (h : f n = f 0) : ∑ k ∈ range n, f (k + 1) = ∑ k ∈ range n, f k := by
  have e1 := Finset.sum_range_succ f n
  have e2 := Finset.sum_range_succ' f n
  rw [e1, h] at e2
  exact (add_right_cancel e2).symm

variable {ι : Type*}

/-! ## Cycles of a permutation of prime order -/

section Cycles

variable [Fintype ι] [DecidableEq ι] (g : Perm ι)

/-- The cycle of `g` through `i`: the orbit of `i` under `⟨g⟩`, which is `{i}` when `g i = i`. -/
def cyc (i : ι) : Finset ι :=
  univ.filter (fun j => g.SameCycle i j)

theorem mem_cyc {i j : ι} : j ∈ cyc g i ↔ g.SameCycle i j := by
  simp [cyc]

theorem cyc_of_apply_eq {i : ι} (hi : g i = i) : cyc g i = {i} := by
  ext j
  rw [mem_cyc, Finset.mem_singleton]
  constructor
  · intro h
    exact (h.eq_of_left hi).symm
  · rintro rfl
    exact SameCycle.refl g j

theorem cyc_eq_support_cycleOf {i : ι} (hi : g i ≠ i) : cyc g i = (g.cycleOf i).support := by
  ext j
  rw [mem_cyc, mem_support_cycleOf_iff' hi]

theorem card_cyc_of_apply_ne (hp : (orderOf g).Prime) {i : ι} (hi : g i ≠ i) :
    #(cyc g i) = orderOf g := by
  rw [cyc_eq_support_cycleOf g hi, ← (isCycle_cycleOf g hi).orderOf]
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_cycleOf_dvd_orderOf g i) with h | h
  · rw [orderOf_eq_one_iff, cycleOf_eq_one_iff] at h
    exact absurd h hi
  · exact h

/-- The orbits of `⟨g⟩` have size `1` or `p`. -/
theorem card_cyc {p : ℕ} (hp : p.Prime) (hg : orderOf g = p) (i : ι) :
    #(cyc g i) = 1 ∨ #(cyc g i) = p := by
  by_cases hi : g i = i
  · left
    rw [cyc_of_apply_eq g hi, Finset.card_singleton]
  · right
    rw [← hg]
    exact card_cyc_of_apply_ne g (by rw [hg]; exact hp) hi

/-- On a cycle of length `p = ord g`, `k ↦ g^k i` (`k < p`) runs once through the cycle. -/
theorem sum_cyc_eq_sum_range {M : Type*} [AddCommMonoid M] (hp : (orderOf g).Prime) {i : ι}
    (hi : g i ≠ i) (v : ι → M) :
    ∑ j ∈ cyc g i, v j = ∑ k ∈ range (orderOf g), v ((g ^ k) i) := by
  have hcyc : g.IsCycleOn (cyc g i : Set ι) := by
    rw [cyc_eq_support_cycleOf g hi]
    exact isCycleOn_support_cycleOf g i
  have hmem : i ∈ cyc g i := (mem_cyc g).2 (SameCycle.refl g i)
  symm
  apply Finset.sum_nbij (fun k => (g ^ k) i)
  · intro k _
    rw [mem_cyc]
    exact ⟨(k : ℤ), by rw [zpow_natCast]⟩
  · intro a ha b hb hab
    have h := (hcyc.pow_apply_eq_pow_apply hmem).1 hab
    rw [card_cyc_of_apply_ne g hp hi] at h
    exact Nat.ModEq.eq_of_lt_of_lt h (Finset.mem_range.1 (Finset.mem_coe.1 ha))
      (Finset.mem_range.1 (Finset.mem_coe.1 hb))
  · intro j hj
    obtain ⟨k, hk, hkj⟩ := ((mem_cyc g).1 (Finset.mem_coe.1 hj)).exists_pow_eq'
    exact ⟨k, Finset.mem_coe.2 (Finset.mem_range.2 hk), hkj⟩
  · intro k _
    rfl

end Cycles

/-! ## The map `e₀` -/

section E0

variable (g : Perm ι)

/-- `e₀ v`, with `(e₀ v) i = ∑_{k < ord g} v (g^k i)`. -/
noncomputable def e0 : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun v i := ∑ k ∈ range (orderOf g), v ((g ^ k) i)
  map_add' v w := by
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp [Finset.mul_sum]

theorem e0_apply (v : ι → ZMod 2) (i : ι) : e0 g v i = ∑ k ∈ range (orderOf g), v ((g ^ k) i) :=
  rfl

/-- `v g = v` iff `v` is constant along `g`. -/
theorem permute_eq_self_iff {v : ι → ZMod 2} : permute g v = v ↔ ∀ i, v (g i) = v i := by
  constructor
  · intro h i
    have := congrFun h (g i)
    rw [permute_apply, Equiv.symm_apply_apply] at this
    exact this.symm
  · intro h
    funext i
    rw [permute_apply]
    have := h (g.symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

theorem apply_pow_of_fixed {v : ι → ZMod 2} (hv : ∀ i, v (g i) = v i) (k : ℕ) (i : ι) :
    v ((g ^ k) i) = v i := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, hv, ih]

/-- On words fixed by `g`, `e₀` is multiplication by `ord g`. -/
theorem e0_of_fixed {v : ι → ZMod 2} (hv : ∀ i, v (g i) = v i) : e0 g v = (orderOf g) • v := by
  funext i
  simp only [e0_apply, apply_pow_of_fixed g hv, Finset.sum_const, Finset.card_range, Pi.smul_apply]

/-- `e₀ v` is fixed by `g`. -/
theorem e0_apply_apply (v : ι → ZMod 2) (i : ι) : e0 g v (g i) = e0 g v i := by
  simp only [e0_apply]
  have h : ∀ k : ℕ, v ((g ^ k) (g i)) = v ((g ^ (k + 1)) i) := fun k => by
    rw [pow_succ, Perm.mul_apply]
  simp only [h]
  exact sum_range_shift_of_periodic (fun k => v ((g ^ k) i)) (orderOf g)
    (by simp only [pow_orderOf_eq_one, pow_zero])

/-- `e₀` maps `C` into `C` when `g ∈ Aut C`. -/
theorem e0_mem {C : Submodule (ZMod 2) (ι → ZMod 2)} (hgC : g ∈ Aut C) {v : ι → ZMod 2}
    (hv : v ∈ C) : e0 g v ∈ C := by
  have h : e0 g v = ∑ k ∈ range (orderOf g), permute (g ^ k)⁻¹ v := by
    funext i
    simp only [e0_apply, Finset.sum_apply, permute_inv_apply]
  rw [h]
  refine Submodule.sum_mem C (fun k _ => ?_)
  exact permute_mem_of_mem_Aut ((Aut C).inv_mem ((Aut C).pow_mem hgC k)) hv

/-- `e₀` is idempotent when `ord g` is odd. -/
theorem e0_e0 (hodd : Odd (orderOf g)) (v : ι → ZMod 2) : e0 g (e0 g v) = e0 g v := by
  rw [e0_of_fixed g (e0_apply_apply g v)]
  funext i
  exact nsmul_odd hodd _

/-- A word fixed by `g` is orthogonal to every word `e` with `e₀ e = 0`. -/
theorem dotProduct_eq_zero_of_fixed [Fintype ι] (hodd : Odd (orderOf g)) {f e : ι → ZMod 2}
    (hf : ∀ i, f (g i) = f i) (he : e0 g e = 0) : f ⬝ᵥ e = 0 := by
  have key : ∀ k : ℕ, f ⬝ᵥ e = ∑ i, f i * e ((g ^ k) i) := by
    intro k
    simp only [dotProduct]
    rw [← Equiv.sum_comp (g ^ k) (fun i => f i * e i)]
    simp only [apply_pow_of_fixed g hf]
  calc f ⬝ᵥ e = (orderOf g) • (f ⬝ᵥ e) := (nsmul_odd hodd _).symm
    _ = ∑ _k ∈ range (orderOf g), f ⬝ᵥ e := by rw [Finset.sum_const, Finset.card_range]
    _ = ∑ k ∈ range (orderOf g), ∑ i, f i * e ((g ^ k) i) :=
        Finset.sum_congr rfl (fun k _ => key k)
    _ = ∑ i, f i * e0 g e i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [e0_apply, Finset.mul_sum]
    _ = 0 := by simp [he]

end E0

/-! ## The subcodes `F` and `E` -/

section FE

/-- `F_g(C) = {v ∈ C | v g = v}`: the words of `C` fixed by `g`. -/
def Fsub (C : Submodule (ZMod 2) (ι → ZMod 2)) (g : Perm ι) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | v ∈ C ∧ permute g v = v}
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    exact ⟨C.add_mem hv hw, by rw [map_add, hv', hw']⟩
  zero_mem' := ⟨C.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    exact ⟨C.smul_mem c hv, by rw [map_smul, hv']⟩

theorem Fsub_le (C : Submodule (ZMod 2) (ι → ZMod 2)) (g : Perm ι) : Fsub C g ≤ C :=
  fun _ h => h.1

theorem mem_Fsub_iff {C : Submodule (ZMod 2) (ι → ZMod 2)} {g : Perm ι} {v : ι → ZMod 2} :
    v ∈ Fsub C g ↔ v ∈ C ∧ ∀ i, v (g i) = v i := by
  show (v ∈ C ∧ permute g v = v) ↔ _
  rw [permute_eq_self_iff]

variable [Fintype ι] [DecidableEq ι]

/-- The weight of `v` on the cycle of `g` through `i`. -/
def wtOn (g : Perm ι) (v : ι → ZMod 2) (i : ι) : ℕ :=
  #((cyc g i).filter (fun j => v j ≠ 0))

/-- `E_g(C)`: the words of `C` that vanish on the fixed points of `g` and have even weight on each
cycle of `g`. -/
def Esub (C : Submodule (ZMod 2) (ι → ZMod 2)) (g : Perm ι) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | v ∈ C ∧ (∀ i, g i = i → v i = 0) ∧ ∀ i, g i ≠ i → Even (wtOn g v i)}
  add_mem' := by
    rintro v w ⟨hv, hv0, hv1⟩ ⟨hw, hw0, hw1⟩
    refine ⟨C.add_mem hv hw, fun i hi => ?_, fun i hi => ?_⟩
    · simp [hv0 i hi, hw0 i hi]
    · have h1 := (even_card_filter_ne_zero_iff _ _).1 (hv1 i hi)
      have h2 := (even_card_filter_ne_zero_iff _ _).1 (hw1 i hi)
      refine (even_card_filter_ne_zero_iff _ _).2 ?_
      simp only [Pi.add_apply, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' := ⟨C.zero_mem, fun _ _ => rfl, fun i _ => by simp [wtOn]⟩
  smul_mem' := by
    rintro c v ⟨hv, hv0, hv1⟩
    refine ⟨C.smul_mem c hv, fun i hi => ?_, fun i hi => ?_⟩
    · simp [hv0 i hi]
    · have h1 := (even_card_filter_ne_zero_iff _ _).1 (hv1 i hi)
      refine (even_card_filter_ne_zero_iff _ _).2 ?_
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h1, mul_zero]

theorem Esub_le (C : Submodule (ZMod 2) (ι → ZMod 2)) (g : Perm ι) : Esub C g ≤ C :=
  fun _ h => h.1

variable {C : Submodule (ZMod 2) (ι → ZMod 2)} {g : Perm ι}

/-- For `g` of odd prime order, `E_g(C) = {v ∈ C | e₀ v = 0}`. -/
theorem mem_Esub_iff (hp : (orderOf g).Prime) (hodd : Odd (orderOf g)) {v : ι → ZMod 2} :
    v ∈ Esub C g ↔ v ∈ C ∧ e0 g v = 0 := by
  constructor
  · rintro ⟨hv, hv0, hv1⟩
    refine ⟨hv, funext fun i => ?_⟩
    by_cases hi : g i = i
    · have hk : ∀ k : ℕ, (g ^ k) i = i := fun k => pow_apply_eq_self_of_apply_eq_self hi k
      rw [e0_apply, Pi.zero_apply]
      simp only [hk, Finset.sum_const, Finset.card_range, nsmul_odd hodd, hv0 i hi]
    · rw [e0_apply, Pi.zero_apply, ← sum_cyc_eq_sum_range g hp hi]
      exact (even_card_filter_ne_zero_iff _ _).1 (hv1 i hi)
  · rintro ⟨hv, he⟩
    refine ⟨hv, fun i hi => ?_, fun i hi => ?_⟩
    · have h := congrFun he i
      have hk : ∀ k : ℕ, (g ^ k) i = i := fun k => pow_apply_eq_self_of_apply_eq_self hi k
      rw [e0_apply, Pi.zero_apply] at h
      simpa only [hk, Finset.sum_const, Finset.card_range, nsmul_odd hodd] using h
    · have h := congrFun he i
      rw [e0_apply, Pi.zero_apply, ← sum_cyc_eq_sum_range g hp hi] at h
      exact (even_card_filter_ne_zero_iff _ _).2 h

/-- **`C = F + E`.** -/
theorem Fsub_sup_Esub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p) (hgC : g ∈ Aut C) :
    Fsub C g ⊔ Esub C g = C := by
  have hp' : (orderOf g).Prime := by rw [hg]; exact hp
  have hodd : Odd (orderOf g) := by rw [hg]; exact hp.odd_of_ne_two hp2
  apply le_antisymm (sup_le (Fsub_le C g) (Esub_le C g))
  intro v hv
  have hsplit : e0 g v + (v + e0 g v) = v := by
    rw [← add_assoc, add_comm (e0 g v) v, add_assoc, vec_add_self, add_zero]
  rw [← hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · exact mem_Fsub_iff.2 ⟨e0_mem g hgC hv, e0_apply_apply g v⟩
  · rw [mem_Esub_iff hp' hodd]
    refine ⟨C.add_mem hv (e0_mem g hgC hv), ?_⟩
    rw [map_add, e0_e0 g hodd, vec_add_self]

/-- **`F ∩ E = 0`.** -/
theorem Fsub_inf_Esub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p) :
    Fsub C g ⊓ Esub C g = ⊥ := by
  have hp' : (orderOf g).Prime := by rw [hg]; exact hp
  have hodd : Odd (orderOf g) := by rw [hg]; exact hp.odd_of_ne_two hp2
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [Submodule.mem_bot]
  have h1 : e0 g v = v := by
    rw [e0_of_fixed g (mem_Fsub_iff.1 hv.1).2]
    funext i
    exact nsmul_odd hodd _
  have h2 : e0 g v = 0 := ((mem_Esub_iff hp' hodd).1 hv.2).2
  rw [← h1, h2]

/-- **`F ⊥ E`.** -/
theorem Fsub_orthogonal_Esub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p) :
    ∀ f ∈ Fsub C g, ∀ e ∈ Esub C g, f ⬝ᵥ e = 0 := by
  have hp' : (orderOf g).Prime := by rw [hg]; exact hp
  have hodd : Odd (orderOf g) := by rw [hg]; exact hp.odd_of_ne_two hp2
  intro f hf e he
  exact dotProduct_eq_zero_of_fixed g hodd (mem_Fsub_iff.1 hf).2 ((mem_Esub_iff hp' hodd).1 he).2

/-- **Decomposition theorem** [Huf82, Yor83]: for `g ∈ Aut C` of odd prime order, `C = F ⊕ E` with
`F ⊥ E`. -/
theorem decomposition {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p) (hgC : g ∈ Aut C) :
    Fsub C g ⊔ Esub C g = C ∧ Fsub C g ⊓ Esub C g = ⊥ ∧
      ∀ f ∈ Fsub C g, ∀ e ∈ Esub C g, f ⬝ᵥ e = 0 :=
  ⟨Fsub_sup_Esub hp hp2 hg hgC, Fsub_inf_Esub hp hp2 hg, Fsub_orthogonal_Esub hp hp2 hg⟩

end FE

/-! ## The contracted fixed code -/

section Contracted

variable (g : Perm ι)

/-- The orbits of `⟨g⟩`: the cycles of `g`, fixed points included. -/
def Orbits : Type _ :=
  Quotient (SameCycle.setoid g)

/-- The orbit of the coordinate `i`. -/
def toOrbit (i : ι) : Orbits g :=
  Quotient.mk (SameCycle.setoid g) i

theorem toOrbit_surjective : Function.Surjective (toOrbit g) :=
  Quotient.mk_surjective

theorem toOrbit_eq_toOrbit {i j : ι} : toOrbit g i = toOrbit g j ↔ g.SameCycle i j :=
  Quotient.eq

theorem toOrbit_apply (i : ι) : toOrbit g (g i) = toOrbit g i :=
  (toOrbit_eq_toOrbit g).2 (sameCycle_apply_left.2 (SameCycle.refl g i))

/-- `φ₀`: repeats the value `u ω` on every coordinate of the orbit `ω`. -/
def expand : (Orbits g → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (toOrbit g)

theorem expand_apply (u : Orbits g → ZMod 2) (i : ι) : expand g u i = u (toOrbit g i) :=
  rfl

theorem expand_apply_apply (u : Orbits g → ZMod 2) (i : ι) : expand g u (g i) = expand g u i := by
  rw [expand_apply, expand_apply, toOrbit_apply]

/-- The contracted fixed code `C₀ = {u | φ₀ u ∈ C}`: one coordinate for each orbit of `⟨g⟩`. -/
def contracted (C : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (Orbits g → ZMod 2) :=
  C.comap (expand g)

theorem mem_contracted {C : Submodule (ZMod 2) (ι → ZMod 2)} {u : Orbits g → ZMod 2} :
    u ∈ contracted g C ↔ expand g u ∈ C :=
  Iff.rfl

variable [Fintype ι] [DecidableEq ι]

instance : DecidableEq (Orbits g) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun i j =>
    decidable_of_iff (g.SameCycle i j) (toOrbit_eq_toOrbit g).symm

instance : Fintype (Orbits g) :=
  @Quotient.fintype ι _ (SameCycle.setoid g) (fun i j => inferInstanceAs (Decidable (g.SameCycle i j)))

omit [DecidableEq ι] in
/-- Every word fixed by `g` is `φ₀ u` for some `u`. -/
theorem exists_expand_eq {v : ι → ZMod 2} (hv : ∀ i, v (g i) = v i) : ∃ u, expand g u = v := by
  refine ⟨Quotient.lift v (fun a b (hab : g.SameCycle a b) => ?_), ?_⟩
  · obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
    rw [← hk, apply_pow_of_fixed g hv]
  · funext i
    rfl

omit [DecidableEq ι] in
/-- `F = φ₀(C₀)`. -/
theorem Fsub_eq_map_contracted (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Fsub C g = (contracted g C).map (expand g) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvC, hvfix⟩ := mem_Fsub_iff.1 hv
    obtain ⟨u, rfl⟩ := exists_expand_eq g hvfix
    exact Submodule.mem_map.2 ⟨u, hvC, rfl⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
    exact mem_Fsub_iff.2 ⟨hu, expand_apply_apply g u⟩

/-- Every orbit has an odd number of elements when `ord g` is an odd prime. -/
theorem odd_card_fiber (hp : (orderOf g).Prime) (hodd : Odd (orderOf g)) (ω : Orbits g) :
    Odd #(univ.filter (fun i => toOrbit g i = ω)) := by
  obtain ⟨i₀, rfl⟩ := toOrbit_surjective g ω
  have h : univ.filter (fun i => toOrbit g i = toOrbit g i₀) = cyc g i₀ := by
    ext j
    rw [Finset.mem_filter, mem_cyc, toOrbit_eq_toOrbit]
    exact ⟨fun h => h.2.symm, fun h => ⟨Finset.mem_univ _, h.symm⟩⟩
  rw [h]
  by_cases hi : g i₀ = i₀
  · rw [cyc_of_apply_eq g hi, Finset.card_singleton]
    exact odd_one
  · rw [card_cyc_of_apply_ne g hp hi]
    exact hodd

/-- `⟨φ₀ u, φ₀ u'⟩ = ⟨u, u'⟩` when every orbit has odd size. -/
theorem expand_dotProduct (hp : (orderOf g).Prime) (hodd : Odd (orderOf g))
    (u u' : Orbits g → ZMod 2) : expand g u ⬝ᵥ expand g u' = u ⬝ᵥ u' := by
  simp only [dotProduct, expand_apply]
  rw [Finset.sum_comp (fun ω => u ω * u' ω) (toOrbit g),
    Finset.image_univ_of_surjective (toOrbit_surjective g)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  exact nsmul_odd (odd_card_fiber g hp hodd ω) _

/-- **The contracted fixed code is self-dual** when `C` is self-dual [Huf82]. -/
theorem contracted_selfDual {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p)
    {C : Submodule (ZMod 2) (ι → ZMod 2)} (hgC : g ∈ Aut C) (hC : SelfDual C) :
    SelfDual (contracted g C) := by
  have hp' : (orderOf g).Prime := by rw [hg]; exact hp
  have hodd : Odd (orderOf g) := by rw [hg]; exact hp.odd_of_ne_two hp2
  unfold SelfDual
  apply le_antisymm
  · intro u hu
    rw [mem_dual]
    intro u' hu'
    rw [← expand_dotProduct g hp' hodd]
    have h1 : expand g u ∈ dual C := by
      rw [← hC]
      exact hu
    exact (mem_dual.1 h1) _ hu'
  · intro u hu
    rw [mem_contracted, hC, mem_dual]
    intro c hc
    have hsplit : e0 g c + (c + e0 g c) = c := by
      rw [← add_assoc, add_comm (e0 g c) c, add_assoc, vec_add_self, add_zero]
    have hF : e0 g c ∈ Fsub C g := mem_Fsub_iff.2 ⟨e0_mem g hgC hc, e0_apply_apply g c⟩
    rw [Fsub_eq_map_contracted] at hF
    obtain ⟨u'', hu'', he⟩ := Submodule.mem_map.1 hF
    have h1 : expand g u ⬝ᵥ e0 g c = 0 := by
      rw [← he, expand_dotProduct g hp' hodd]
      exact (mem_dual.1 hu) u'' hu''
    have h2 : expand g u ⬝ᵥ (c + e0 g c) = 0 := by
      apply dotProduct_eq_zero_of_fixed g hodd (expand_apply_apply g u)
      rw [map_add, e0_e0 g hodd, vec_add_self]
    rw [← hsplit, dotProduct_add, h1, h2, add_zero]

end Contracted

end C72
