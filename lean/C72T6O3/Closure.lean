import C72T2.OctDod
import C72T2.TheoremB

/-!
# T6 (order 3): octads under automorphisms, and a fixed-point closure certificate

* `wt_add_binary`: `|x + y| + 2 |x ∩ y| = |x| + |y|` for binary words; with the weights of `G24`, two octads that
  share at least 5 points are equal (`eq_of_five`), so an automorphism of `G24` that fixes 5 points of an octad
  maps the octad onto itself (`map_octad_eq`).
* The closure certificate (`eq_one_of_fixes`): an automorphism of `G24` that fixes the points `0, 1, 2, 3, 4, 7`
  (`p₁, …, p₆`) and `5` (`q₁`) is the identity. Proof: if `h` fixes every point of a set `F`, then `h` maps every
  octad with at least 5 points in `F` onto itself; so `h(y)` lies in the cell of `y` (the intersection, over these
  octads, of the octad if it contains `y` and of its complement otherwise), and `h(y) = y` when the cell is `{y}`.
  A Bool computation (`closeIter`, on bit masks, over the 759 octads of `octdod.txt`) adds such points to `F`; from
  `F₀ = {0, 1, 2, 3, 4, 5, 7}` two rounds reach all 24 points (`closeIter_F0`, kernel check), and `closeIter_sound`
  is the soundness lemma.
-/

namespace C72.Three.M24

open Equiv Finset

/-! ## Octads under automorphisms -/

/-- For binary words, `|x + y| + 2 |x ∩ y| = |x| + |y|`. -/
theorem wt_add_binary {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ZMod 2) :
    wt (x + y) + 2 * #(supp x ∩ supp y) = wt x + wt y := by
  have hinter : #(supp x ∩ supp y) = ∑ i, if x i ≠ 0 ∧ y i ≠ 0 then 1 else 0 := by
    rw [supp, supp, ← Finset.filter_and, Finset.card_filter]
  rw [wt_eq_sum (x + y), wt_eq_sum x, wt_eq_sum y, hinter, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  have key : ∀ a b : ZMod 2, ((if a + b ≠ 0 then 1 else 0) : ℕ) + 2 * (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) =
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
    decide
  exact key (x i) (y i)

/-- Two words of weight 8 of `G24` whose supports share at least 5 points are equal. -/
theorem eq_of_five {x x' : Fin 24 → ZMod 2} (hx : x ∈ G24) (hx' : x' ∈ G24) (h8 : wt x = 8)
    (h8' : wt x' = 8) (h5 : 5 ≤ #(supp x ∩ supp x')) : x = x' := by
  have hsum := wt_add_binary x x'
  have hw := G24_wt (G24.add_mem hx hx')
  have h0 : wt (x + x') = 0 := by
    rcases hw with h | h | h | h | h <;> omega
  have hz := wt_eq_zero.1 h0
  funext i
  have hi := congrFun hz i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    decide
  exact key _ _ hi

/-- An automorphism maps octads to octads. -/
theorem isOctad_map {m : Perm (Fin 24)} (hm : m ∈ Aut G24) {O : Finset (Fin 24)} (hO : IsOctad O) :
    IsOctad (O.map m.toEmbedding) := by
  obtain ⟨x, hx, hx8, rfl⟩ := hO
  exact ⟨permute m x, permute_mem_of_mem_Aut hm hx, by rw [wt_permute, hx8], supp_permute m x⟩

/-- An automorphism that fixes 5 points of an octad maps the octad onto itself. -/
theorem map_octad_eq {m : Perm (Fin 24)} (hm : m ∈ Aut G24) {O : Finset (Fin 24)} (hO : IsOctad O)
    {S : Finset (Fin 24)} (hS : S ⊆ O) (h5 : 5 ≤ #S) (hfix : ∀ y ∈ S, m y = y) :
    O.map m.toEmbedding = O := by
  obtain ⟨x, hx, hx8, rfl⟩ := hO
  have hmem := permute_mem_of_mem_Aut hm hx
  have hS' : S ⊆ supp (permute m x) := by
    rw [supp_permute]
    intro y hy
    rw [Finset.mem_map]
    exact ⟨y, hS hy, by simp [hfix y hy]⟩
  have h5' : 5 ≤ #(supp (permute m x) ∩ supp x) :=
    le_trans h5 (Finset.card_le_card (Finset.subset_inter hS' hS))
  have heq := eq_of_five hmem hx (by rw [wt_permute, hx8]) hx8 h5'
  rw [← supp_permute, heq]

/-! ## Bit masks -/

theorem mem_supp_toVec {m : ℕ} {i : Fin 24} : i ∈ supp (toVec m) ↔ m.testBit i.val = true := by
  cases h : m.testBit i.val <;> simp [mem_supp, toVec, h]

theorem supp_toVec_land (a b : ℕ) : supp (toVec (a &&& b)) = supp (toVec a) ∩ supp (toVec b) := by
  ext i
  simp only [Finset.mem_inter, mem_supp_toVec, Nat.testBit_and, Bool.and_eq_true]

/-- `2²⁴ - 1`, the mask of all 24 points. -/
def FULL : ℕ :=
  16777215

theorem testBit_FULL : ∀ z : Fin 24, FULL.testBit z.val = true := by
  decide

/-! ## The closure computation -/

/-- The cell of `y` for the octad masks `L`: the intersection of each mask if it contains `y` and of its
complement otherwise. -/
def cell (y : ℕ) : List ℕ → ℕ
  | [] => FULL
  | o :: os => (if o.testBit y then o else FULL ^^^ o) &&& cell y os

/-- Adds to `F` the points `y < n` whose cell is `{y}`. -/
def addFixed (F : ℕ) (L : List ℕ) : ℕ → ℕ
  | 0 => F
  | n + 1 => if cell n L == 2 ^ n then addFixed F L n ||| 2 ^ n else addFixed F L n

/-- One round: the cells are taken over the octads with at least 5 points in `F`. -/
def closeRound (F : ℕ) : ℕ :=
  addFixed F (octMasks.filter fun o => 5 ≤ wt (toVec (o &&& F))) 24

/-- `r` rounds. -/
def closeIter : ℕ → ℕ → ℕ
  | 0, F => F
  | r + 1, F => closeIter r (closeRound F)

/-- `F₀ = {0, 1, 2, 3, 4, 5, 7}`: `p₁, …, p₆` and `q₁`. -/
def F0 : ℕ :=
  191

/-- **The kernel check**: from `F₀`, two rounds reach all 24 points. -/
theorem closeIter_F0 : closeIter 2 F0 = FULL := by
  decide +kernel

/-! ## Soundness -/

/-- `h` fixes every point of the mask `F`. -/
def FixesMask (h : Perm (Fin 24)) (F : ℕ) : Prop :=
  ∀ y : Fin 24, F.testBit y.val = true → h y = y

variable {h : Perm (Fin 24)}

/-- An octad with at least 5 points in `F` is mapped onto itself by every automorphism fixing `F`. -/
theorem octad_invariant (hA : h ∈ Aut G24) {F o : ℕ} (hF : FixesMask h F) (ho : o ∈ octMasks)
    (h5 : 5 ≤ wt (toVec (o &&& F))) (z : Fin 24) : o.testBit (h z).val = o.testBit z.val := by
  have hO : IsOctad (supp (toVec o)) := isOctad_iff.2 ⟨o, ho, rfl⟩
  have hinv : (supp (toVec o)).map h.toEmbedding = supp (toVec o) := by
    refine map_octad_eq hA hO (S := supp (toVec (o &&& F))) ?_ ?_ ?_
    · rw [supp_toVec_land]
      exact Finset.inter_subset_left
    · rw [card_supp]
      exact h5
    · intro y hy
      rw [supp_toVec_land, Finset.mem_inter, mem_supp_toVec, mem_supp_toVec] at hy
      exact hF y hy.2
  have key : h z ∈ supp (toVec o) ↔ z ∈ supp (toVec o) := by
    constructor
    · intro hz
      rw [← hinv, Finset.mem_map] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hwz' : w = z := h.injective (by simpa using hwz)
      rw [← hwz']
      exact hw
    · intro hz
      rw [← hinv, Finset.mem_map]
      exact ⟨z, hz, rfl⟩
  rw [mem_supp_toVec, mem_supp_toVec] at key
  cases h1 : o.testBit (h z).val <;> cases h2 : o.testBit z.val <;> simp_all

/-- Soundness of `cell`: a point `z` that agrees with `y` on every mask of `L` lies in the cell of `y`. -/
theorem testBit_cell (y z : Fin 24) :
    ∀ L : List ℕ, (∀ o ∈ L, o.testBit z.val = o.testBit y.val) → (cell y.val L).testBit z.val = true
  | [] => fun _ => testBit_FULL z
  | o :: os => fun hL => by
    have hrest := testBit_cell y z os (fun o' ho' => hL o' (List.mem_cons_of_mem _ ho'))
    have ho := hL o List.mem_cons_self
    rw [cell, Nat.testBit_and, hrest, Bool.and_true]
    by_cases hy : o.testBit y.val = true
    · rw [ite_eq_left hy, ho, hy]
    · rw [ite_eq_right hy, Nat.testBit_xor, testBit_FULL z, ho]
      simpa using hy

theorem eq_of_cell {y z : Fin 24} {L : List ℕ} (hc : cell y.val L = 2 ^ y.val)
    (ht : (cell y.val L).testBit z.val = true) : z = y := by
  rw [hc, Nat.testBit_two_pow] at ht
  have hyz : y.val = z.val := by simpa using ht
  exact Fin.ext hyz.symm

theorem addFixed_spec (F : ℕ) (L : List ℕ) : ∀ (n : ℕ) (y : Fin 24), (addFixed F L n).testBit y.val = true →
    F.testBit y.val = true ∨ cell y.val L = 2 ^ y.val
  | 0, y, hy => Or.inl hy
  | n + 1, y, hy => by
    simp only [addFixed] at hy
    split_ifs at hy with hc
    · rw [Nat.testBit_or, Bool.or_eq_true] at hy
      rcases hy with hy | hy
      · exact addFixed_spec F L n y hy
      · rw [Nat.testBit_two_pow] at hy
        have hn : n = y.val := by simpa using hy
        subst hn
        exact Or.inr (by simpa using hc)
    · exact addFixed_spec F L n y hy

/-- Soundness of one round. -/
theorem closeRound_sound (hA : h ∈ Aut G24) {F : ℕ} (hF : FixesMask h F) : FixesMask h (closeRound F) := by
  intro y hy
  rcases addFixed_spec F _ 24 y hy with h1 | hc
  · exact hF y h1
  · refine eq_of_cell hc (testBit_cell y (h y) _ ?_)
    intro o ho
    rw [List.mem_filter] at ho
    exact octad_invariant hA hF ho.1 (by simpa using ho.2) y

theorem closeIter_sound (hA : h ∈ Aut G24) : ∀ (r : ℕ) (F : ℕ), FixesMask h F → FixesMask h (closeIter r F)
  | 0, _, hF => hF
  | r + 1, _, hF => closeIter_sound hA r _ (closeRound_sound hA hF)

/-- **An automorphism of `G24` fixing `0, 1, 2, 3, 4, 7` (`p₁, …, p₆`) and `5` (`q₁`) is the identity.** -/
theorem eq_one_of_fixes (hA : h ∈ Aut G24)
    (hfix : ∀ y : Fin 24, y ∈ ({0, 1, 2, 3, 4, 7, 5} : Finset (Fin 24)) → h y = y) : h = 1 := by
  have hmask : ∀ y : Fin 24, F0.testBit y.val = true → y ∈ ({0, 1, 2, 3, 4, 7, 5} : Finset (Fin 24)) := by
    decide
  have hF : FixesMask h F0 := fun y hy => hfix y (hmask y hy)
  have hall := closeIter_sound hA 2 F0 hF
  rw [closeIter_F0] at hall
  exact Equiv.ext fun y => by rw [Perm.one_apply]; exact hall y (testBit_FULL y)

end C72.Three.M24
