import C72T1.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin

/-!
# T1: the labelling lemma

A permutation `g` of `Fin n` of prime order `p` with `f` fixed points is conjugate to the standard permutation
`stdPerm c p f h` (`h : c * p + f = n`): the `a`-th cycle is `{p a, p a + 1, …, p a + p - 1}` with `g` acting as
the cyclic shift `p a + b ↦ p a + (b + 1 mod p)`, and the points `c p, …, n - 1` are fixed. For `p = 5` this is the
numbering of the paper (Section 2.1: cycles `{5i, …, 5i+4}`, fixed points 70 and 71); for `p = 3` (Section 4.1) and
`p = 2` (Section 3) the paper labels the coordinates by pairs `(i, j)`, and `stdPerm` numbers them as `p k + j`.

For a code, `exists_relabel` turns `g ∈ Aut C` into `stdPerm c p f h ∈ Aut (C π)` for a relabelling `π`.
-/

namespace C72

open Equiv Equiv.Perm Finset

/-- `Fin (c * p + f)` as `c` blocks `Fin c × Fin p` followed by `f` points: `(a, b) ↦ b + p * a`
(`finProdFinEquiv`) and `x ↦ c * p + x` (`finSumFinEquiv`). -/
def blockEquiv (c p f : ℕ) : (Fin c × Fin p) ⊕ Fin f ≃ Fin (c * p + f) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- The standard shift `(a, b) ↦ (a, b + 1)` on the blocks and the identity on the last `f` points. -/
def stdShift (c p f : ℕ) : Perm ((Fin c × Fin p) ⊕ Fin f) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) (finRotate p)) (Equiv.refl _)

/-- The standard permutation of `Fin n`, `n = c * p + f`: the `a`-th cycle is `{p a, …, p a + p - 1}`, shifted
by one, and `c * p, …, n - 1` are fixed. -/
def stdPerm {n : ℕ} (c p f : ℕ) (h : c * p + f = n) : Perm (Fin n) :=
  ((blockEquiv c p f).trans (finCongr h)).permCongr (stdShift c p f)

theorem permCongr_pow {α β : Type*} (e : α ≃ β) (τ : Perm α) (k : ℕ) :
    (e.permCongr τ) ^ k = e.permCongr (τ ^ k) :=
  (map_pow e.permCongrHom τ k).symm

theorem card_support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (τ : Perm α) : #(e.permCongr τ).support = #τ.support := by
  refine Finset.card_bij (fun x _ => e.symm x) ?_ ?_ ?_
  · intro x hx
    rw [mem_support] at hx ⊢
    intro h
    apply hx
    rw [permCongr_apply, h, Equiv.apply_symm_apply]
  · intro x _ y _ hxy
    exact e.symm.injective hxy
  · intro y hy
    refine ⟨e y, ?_, by simp⟩
    rw [mem_support] at hy ⊢
    rw [permCongr_apply, Equiv.symm_apply_apply]
    intro h
    exact hy (e.injective h)

theorem stdShift_pow_inl (c p f k : ℕ) (a : Fin c) (b : Fin p) :
    (stdShift c p f ^ k) (Sum.inl (a, b)) = Sum.inl (a, (finRotate p ^ k) b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    rfl

theorem stdShift_pow_inr (c p f k : ℕ) (x : Fin f) :
    (stdShift c p f ^ k) (Sum.inr x) = Sum.inr x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih]
    rfl

theorem stdShift_pow_prime {c p f : ℕ} (hp : p.Prime) : stdShift c p f ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hrot : finRotate p ^ p = 1 := by
    rw [pow_prime_eq_one_iff, cycleType_finRotate_of_le hp.two_le]
    simp
  ext x
  rcases x with ⟨a, b⟩ | x
  · rw [stdShift_pow_inl, hrot]
    rfl
  · rw [stdShift_pow_inr]
    rfl

theorem card_support_stdShift {c p f : ℕ} (hp : 2 ≤ p) : #(stdShift c p f).support = c * p := by
  have h : (stdShift c p f).support = (univ : Finset (Fin c × Fin p)).map Function.Embedding.inl := by
    ext x
    rcases x with ⟨a, b⟩ | x
    · rw [mem_support, Finset.mem_map]
      constructor
      · intro _
        exact ⟨(a, b), Finset.mem_univ _, rfl⟩
      · intro _ heq
        have hb : b ∈ (finRotate p).support := by
          rw [support_finRotate_of_le hp]
          exact Finset.mem_univ b
        apply (mem_support.1 hb)
        have h2 : (Sum.inl (a, finRotate p b) : (Fin c × Fin p) ⊕ Fin f) = Sum.inl (a, b) := heq
        simpa using h2
    · rw [mem_support, Finset.mem_map]
      constructor
      · intro hx
        exact absurd rfl hx
      · rintro ⟨y, _, hy⟩
        exact absurd hy Sum.inl_ne_inr
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **Labelling lemma.** A permutation of `Fin n` of prime order `p` with `f` fixed points is conjugate to
`stdPerm c p f h` (`c` cycles of length `p`, `c * p + f = n`). -/
theorem labelling {n p : ℕ} (hp : p.Prime) {g : Perm (Fin n)} (hg : orderOf g = p) :
    ∃ (c f : ℕ) (h : c * p + f = n), f = #(univ.filter fun i => g i = i) ∧
      ∃ π : Perm (Fin n), π * g * π⁻¹ = stdPerm c p f h := by
  have : Fact p.Prime := ⟨hp⟩
  have hgp : g ^ p = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hct : g.cycleType = Multiset.replicate g.cycleType.card p := cycleType_of_pow_prime_eq_one hgp
  have hsupp : #g.support = g.cycleType.card * p := by
    rw [← sum_cycleType, hct, Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
  have hn : g.cycleType.card * p + #(univ.filter fun i => g i = i) = n := by
    rw [← hsupp, add_comm]
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i => g i = i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  refine ⟨g.cycleType.card, _, hn, rfl, ?_⟩
  set m := g.cycleType.card with hm
  have hσp : stdPerm m p _ hn ^ p = 1 := by
    unfold stdPerm
    rw [permCongr_pow, stdShift_pow_prime hp]
    ext x
    simp
  have hσsupp : #(stdPerm m p _ hn).support = m * p := by
    unfold stdPerm
    rw [card_support_permCongr, card_support_stdShift hp.two_le]
  have hσct : (stdPerm m p _ hn).cycleType = Multiset.replicate m p := by
    have hct' := cycleType_of_pow_prime_eq_one hσp
    have hsum := sum_cycleType (stdPerm m p _ hn)
    rw [hct', Multiset.sum_replicate, smul_eq_mul, hσsupp] at hsum
    rw [hct', Nat.eq_of_mul_eq_mul_right hp.pos hsum]
  exact isConj_iff.1 (isConj_iff_cycleType_eq.2 (hct.trans hσct.symm))

/-- **Relabelling.** For `g ∈ Aut C` of prime order `p` there is a permutation `π` of the coordinates such
that the standard permutation is an automorphism of the relabelled code `C π`. The code `C π` is extremal
when `C` is (`Ext72.map_permute`). -/
theorem exists_relabel {n p : ℕ} (hp : p.Prime) {C : Code n} {g : Perm (Fin n)} (hgC : g ∈ Aut C)
    (hg : orderOf g = p) :
    ∃ (c f : ℕ) (h : c * p + f = n) (π : Perm (Fin n)), f = #(univ.filter fun i => g i = i) ∧
      stdPerm c p f h ∈ Aut (C.map (permute π).toLinearMap) := by
  obtain ⟨c, f, h, hf, π, hπ⟩ := labelling hp hg
  refine ⟨c, f, h, π, hf, ?_⟩
  rw [mem_Aut_map_permute_iff, ← hπ]
  have hconj : π⁻¹ * (π * g * π⁻¹) * π = g := by group
  rw [hconj]
  exact hgC

end C72
