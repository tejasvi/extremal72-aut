import C72T1.Labelling
import C72T1.Decomp
import C72T2.Hermitian

/-!
# T2: the coordinates of an automorphism of order 3 (Section 4.1 of the paper)

The paper labels the 72 coordinates `(i, j)`, `1 ≤ i ≤ 24`, `j ∈ ℤ/3`, so that `σ(i, j) = (i, j + 1)`. Here the
`k`-th cycle (`k : Fin 24`) is `{3k, 3k + 1, 3k + 2}` and the coordinate `(k, b)` is `idx k b = 3k + b`; this is the
numbering of T1's `stdPerm 24 3 0` (`sigma3_idx`), so the labelling lemma `exists_relabel` brings every
fixed-point-free automorphism of order 3 to `sigma3`.

* `triple g` is the word `g^{(3)}`, which repeats `g_k` on the `k`-th cycle;
* `phi e` is `φ(e)`, which applies `ψ` on each cycle;
* `σ` acts on `φ(e)` as multiplication by `ω` (`permute_sigma3_phi`) and fixes `g^{(3)}`;
* `|g^{(3)}| = 3|g|`, `|φ(e)| = 2 wt(e)`, `⟨g^{(3)}, g'^{(3)}⟩ = ⟨g, g'⟩`, `⟨g^{(3)}, φ(e)⟩ = 0` and
  `⟨φ(x), φ(y)⟩ = Tr(Σᵢ xᵢ ȳᵢ)`;
* Lemma 4.1: `|g^{(3)} + φ(e)| = 3|g| + 2|S| - 4|g ∩ S|` for `S = supp e` (`lemma41`, without subtraction).
-/

namespace C72.Three

open Equiv Finset F4

/-! ## Coordinates -/

/-- The coordinate `(k, b)`: position `b ∈ ℤ/3` on the `k`-th cycle, numbered `3k + b`. -/
def idx (k : Fin 24) (b : Fin 3) : Fin 72 :=
  ⟨3 * k.val + b.val, by omega⟩

/-- The number `⌊i / 3⌋` of the cycle of the coordinate `i`. -/
def cycNo (i : Fin 72) : Fin 24 :=
  ⟨i.val / 3, by omega⟩

/-- The position `i mod 3` of the coordinate `i` on its cycle. -/
def cycPos (i : Fin 72) : Fin 3 :=
  ⟨i.val % 3, by omega⟩

theorem idx_cycNo_cycPos (i : Fin 72) : idx (cycNo i) (cycPos i) = i := by
  ext
  simp only [idx, cycNo, cycPos]
  omega

theorem cycNo_idx (k : Fin 24) (b : Fin 3) : cycNo (idx k b) = k := by
  ext
  simp only [idx, cycNo]
  have := b.isLt
  omega

theorem cycPos_idx (k : Fin 24) (b : Fin 3) : cycPos (idx k b) = b := by
  ext
  simp only [idx, cycPos]
  have := b.isLt
  omega

theorem exists_idx (i : Fin 72) : ∃ k b, idx k b = i :=
  ⟨cycNo i, cycPos i, idx_cycNo_cycPos i⟩

theorem idx_injective {k k' : Fin 24} {b b' : Fin 3} (h : idx k b = idx k' b') : k = k' ∧ b = b' := by
  constructor
  · rw [← cycNo_idx k b, h, cycNo_idx]
  · rw [← cycPos_idx k b, h, cycPos_idx]

/-- `Fin 24 × Fin 3 ≃ Fin 72`, `(k, b) ↦ 3k + b`. -/
def coordEquiv : Fin 24 × Fin 3 ≃ Fin 72 where
  toFun p := idx p.1 p.2
  invFun i := (cycNo i, cycPos i)
  left_inv p := by simp [cycNo_idx, cycPos_idx]
  right_inv i := idx_cycNo_cycPos i

/-- A sum over the 72 coordinates is a sum over the 24 cycles of the sums over their 3 positions. -/
theorem sum_fin72 {M : Type*} [AddCommMonoid M] (f : Fin 72 → M) :
    ∑ i, f i = ∑ k : Fin 24, ∑ b : Fin 3, f (idx k b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv coordEquiv (fun p => f (idx p.1 p.2)) f (fun _ => rfl)).symm

/-! ## The automorphism `σ` -/

/-- The automorphism of order 3 in the paper's labelling: `σ(k, b) = (k, b + 1)` (`sigma3_idx`). It is T1's
`stdPerm 24 3 0`. -/
def sigma3 : Perm (Fin 72) :=
  stdPerm 24 3 0 rfl

theorem blockEquiv_inl (k : Fin 24) (b : Fin 3) :
    ((blockEquiv 24 3 0).trans (finCongr (rfl : 24 * 3 + 0 = 72))) (Sum.inl (k, b)) = idx k b := by
  apply Fin.ext
  show b.val + 3 * k.val = 3 * k.val + b.val
  omega

theorem sigma3_idx (k : Fin 24) (b : Fin 3) : sigma3 (idx k b) = idx k (b + 1) := by
  rw [sigma3, stdPerm, Equiv.permCongr_apply, ← blockEquiv_inl k b, Equiv.symm_apply_apply,
    ← blockEquiv_inl k (b + 1)]
  congr 1
  simp [stdShift, finRotate_apply]

theorem sigma3_symm_idx (k : Fin 24) (b : Fin 3) : sigma3.symm (idx k b) = idx k (b - 1) := by
  rw [Equiv.symm_apply_eq, sigma3_idx]
  have hb : ∀ b : Fin 3, b - 1 + 1 = b := by decide
  rw [hb b]

theorem sigma3_sq_idx (k : Fin 24) (b : Fin 3) : (sigma3 ^ 2) (idx k b) = idx k (b + 1 + 1) := by
  rw [pow_two, Perm.mul_apply, sigma3_idx, sigma3_idx]

theorem sigma3_pow_three : sigma3 ^ 3 = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [pow_succ, Perm.mul_apply, sigma3_idx, sigma3_sq_idx, Perm.one_apply]
  have hb : ∀ b : Fin 3, b + 1 + 1 + 1 = b := by decide
  rw [hb b]

theorem sigma3_ne_one : sigma3 ≠ 1 := by
  intro h
  have h0 := sigma3_idx 0 0
  rw [h, Perm.one_apply] at h0
  exact absurd (idx_injective h0).2 (by decide)

theorem orderOf_sigma3 : orderOf sigma3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime sigma3_pow_three sigma3_ne_one

/-- `σ` has no fixed point. -/
theorem sigma3_apply_ne (i : Fin 72) : sigma3 i ≠ i := by
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [sigma3_idx]
  intro h
  have hb : ∀ b : Fin 3, b + 1 ≠ b := by decide
  exact hb b (idx_injective h).2

/-- The orbit sum `e₀` of T1 on the `k`-th cycle, from any position `b`. -/
theorem e0_sigma3_idx' (v : Fin 72 → ZMod 2) (k : Fin 24) (b : Fin 3) :
    e0 sigma3 v (idx k b) = v (idx k b) + v (idx k (b + 1)) + v (idx k (b + 1 + 1)) := by
  rw [e0_apply, orderOf_sigma3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one, Perm.one_apply, sigma3_idx, sigma3_sq_idx]

/-- The orbit sum `e₀` of T1 on the `k`-th cycle: `e₀(v)(k, 0) = v(k, 0) + v(k, 1) + v(k, 2)`. -/
theorem e0_sigma3_idx (v : Fin 72 → ZMod 2) (k : Fin 24) :
    e0 sigma3 v (idx k 0) = v (idx k 0) + v (idx k 1) + v (idx k 2) := by
  rw [e0_sigma3_idx']
  rfl

/-! ## The maps `g ↦ g^{(3)}` and `φ` -/

/-- `g ↦ g^{(3)}`: the word that repeats `g_k` on the `k`-th cycle. -/
def triple : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 72 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) cycNo

theorem triple_apply (g : Fin 24 → ZMod 2) (i : Fin 72) : triple g i = g (cycNo i) :=
  rfl

theorem triple_idx (g : Fin 24 → ZMod 2) (k : Fin 24) (b : Fin 3) : triple g (idx k b) = g k := by
  rw [triple_apply, cycNo_idx]

/-- `φ : 𝔽₄²⁴ → 𝔽₂⁷²` applies `ψ` on each cycle: `φ(e)(k, b) = ψ(e_k)_b`. -/
def phi (e : Fin 24 → F4) : Fin 72 → ZMod 2 :=
  fun i => psi (e (cycNo i)) (cycPos i)

theorem phi_idx (e : Fin 24 → F4) (k : Fin 24) (b : Fin 3) : phi e (idx k b) = psi (e k) b := by
  simp only [phi, cycNo_idx, cycPos_idx]

theorem phi_add (e e' : Fin 24 → F4) : phi (e + e') = phi e + phi e' := by
  funext i
  simp only [phi, Pi.add_apply, psi_add]

theorem phi_zero : phi 0 = 0 := by
  funext i
  simp only [phi, Pi.zero_apply, psi_zero]

/-- `σ` acts on `φ(e)` as multiplication by `ω`: `φ(e) σ = φ(ω e)`. -/
theorem permute_sigma3_phi (e : Fin 24 → F4) : permute sigma3 (phi e) = phi (F4.w • e) := by
  funext i
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [permute_apply, sigma3_symm_idx, phi_idx, phi_idx, Pi.smul_apply, smul_eq_mul, psi_w_mul]

/-- `σ` fixes `g^{(3)}`. -/
theorem permute_sigma3_triple (g : Fin 24 → ZMod 2) : permute sigma3 (triple g) = triple g := by
  funext i
  obtain ⟨k, b, rfl⟩ := exists_idx i
  rw [permute_apply, sigma3_symm_idx, triple_idx, triple_idx]

/-! ## Weights and inner products -/

/-- The weight of a binary word of length 72 as a sum over the cycles. -/
theorem wt_eq_sum_cycles (v : Fin 72 → ZMod 2) :
    wt v = ∑ k : Fin 24, ∑ b : Fin 3, if v (idx k b) ≠ 0 then 1 else 0 := by
  rw [wt_eq_sum, sum_fin72]

/-- `|g^{(3)}| = 3|g|`. -/
theorem wt_triple (g : Fin 24 → ZMod 2) : wt (triple g) = 3 * wt g := by
  rw [wt_eq_sum_cycles, wt_eq_sum g, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [triple_idx, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `|φ(e)| = 2 wt(e)`. -/
theorem wt_phi (e : Fin 24 → F4) : wt (phi e) = 2 * wt e := by
  rw [wt_eq_sum_cycles, wt_eq_sum e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [phi_idx]
  exact cycle_wt_psi (e k)

/-- `⟨g^{(3)}, g'^{(3)}⟩ = ⟨g, g'⟩` (every cycle has odd length). -/
theorem dotProduct_triple (g g' : Fin 24 → ZMod 2) : triple g ⬝ᵥ triple g' = g ⬝ᵥ g' := by
  simp only [dotProduct]
  rw [sum_fin72]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [triple_idx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact nsmul_odd ⟨1, rfl⟩ _

/-- `⟨g^{(3)}, φ(e)⟩ = 0` (`ψ(y)` has even weight). -/
theorem dotProduct_triple_phi (g : Fin 24 → ZMod 2) (e : Fin 24 → F4) : triple g ⬝ᵥ phi e = 0 := by
  simp only [dotProduct]
  rw [sum_fin72]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  simp only [triple_idx, phi_idx]
  rw [← Finset.mul_sum, psi_sum, mul_zero]

/-- `⟨φ(x), φ(y)⟩ = Tr(Σᵢ xᵢ ȳᵢ)`, from the trace identity on each cycle. -/
theorem dotProduct_phi (x y : Fin 24 → F4) : phi x ⬝ᵥ phi y = tr (hform x y) := by
  simp only [dotProduct]
  rw [sum_fin72, hform, tr_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [phi_idx]
  exact psi_dot (x k) (y k)

/-- **Lemma 4.1.** For `g ∈ 𝔽₂²⁴` and `e ∈ 𝔽₄²⁴` with support `S`,
`|g^{(3)} + φ(e)| = 3|g| + 2|S| - 4|g ∩ S|`, written here without subtraction. -/
theorem lemma41 (g : Fin 24 → ZMod 2) (e : Fin 24 → F4) :
    wt (triple g + phi e) + 4 * #(supp g ∩ supp e) = 3 * wt g + 2 * wt e := by
  have hinter : #(supp g ∩ supp e) = ∑ k : Fin 24, if g k ≠ 0 ∧ e k ≠ 0 then 1 else 0 := by
    rw [supp, supp, ← Finset.filter_and, Finset.card_filter]
  rw [wt_eq_sum_cycles, wt_eq_sum g, wt_eq_sum e, hinter, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.add_apply, triple_idx, phi_idx]
  exact cycle_weight (g k) (e k)

end C72.Three
