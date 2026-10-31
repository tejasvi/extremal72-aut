import C72T5.CB48Check
import C72T5.CB48Rows
import C72T2.Hermitian
import C72T2.Basic
import C72T3.E8
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# T5: the length-48 analog of `H_CB` is false

`H_CB` (T2) says that no Hermitian self-dual `[24,12,8]` code over `𝔽₄` has a valid labelled Golay code: for every
labelling `π` of `G24`, some octad meets the support of a word of weight 8 in at least 7 points or lies in the support
of a word of weight 10, or some dodecad is the support of a word of weight 12. These are the cases where Lemma 4.1,
`|g^{(3)} + φ(e)| = 3|g| + 2|e| − 4|g ∩ supp e|`, drops below 16.

At length 48 (minimum weight 12) the same computation gives: `G` is a doubly-even self-dual `[16,8,4]` code
(`e8 ⊕ e8` or `d₁₆⁺`, by `H_16`), `E` a Hermitian self-dual `[16,8,6]` code, and the forbidden configurations are a
tetrad (support of a word of weight 4 of `G`) inside the support of a word of weight 6 of `E`, or an octad of `G` equal
to the support of a word of weight 8 of `E` (the conditions (V6), (V8) of the supplement's length-48 test
`order3/labelling/octad_growth/src/control48/lab16.c`). `H_CB48` states that every such `E` and every labelling meet
one of them. The supplement's test shows that it is false: the extended quadratic residue code of length 48 has an
automorphism of order 3 without fixed points, and its codes `D` and `E` (`qr48_DE.txt`) give a valid labelling.

`not_H_CB48` refutes `H_CB48` in Lean with T2's definitions (`F4`, `F4.HSelfDual`, `Three.supp`, T1's `wt`) and T3's
`e8e8`: `E48` (the span of the rows of `C72T5.CB48Rows`) is Hermitian self-dual (`E48_hselfDual`) with minimum weight 6
(`E48_minWt`), and the labelling `piCB` of `e8 ⊕ e8` meets no forbidden configuration (the kernel check
`C72T5.CB48Check.go_all` with the soundness lemma `go_sound`).
-/

namespace C72.T5

open C72 Finset Module

/-! ## The statement -/

/-- A tetrad of a binary code `G` of length 16: the support of a word of weight 4. -/
def IsTetrad16 (G : Code 16) (T : Finset (Fin 16)) : Prop :=
  ∃ x ∈ G, wt x = 4 ∧ Three.supp x = T

/-- An octad of a binary code `G` of length 16: the support of a word of weight 8. -/
def IsOctad16 (G : Code 16) (O : Finset (Fin 16)) : Prop :=
  ∃ x ∈ G, wt x = 8 ∧ Three.supp x = O

/-- **The length-48 analog of `H_CB`**: for every Hermitian self-dual code `E` of length 16 over `𝔽₄` with
minimum weight 6, every labelling `π` of `e8 ⊕ e8` and of `d₁₆⁺` meets a forbidden configuration: a moved tetrad inside
the support of a word of weight 6, or a moved octad equal to the support of a word of weight 8. -/
def H_CB48 : Prop :=
  ∀ E : Submodule F4 (Fin 16 → F4), F4.HSelfDual E → (∀ e ∈ E, e ≠ 0 → 6 ≤ wt e) → (∃ e ∈ E, wt e = 6) →
    ∀ G ∈ ({T3.e8e8, T3.d16plus} : Set (Code 16)), ∀ π : Equiv.Perm (Fin 16),
      (∃ T, IsTetrad16 G T ∧ ∃ e ∈ E, wt e = 6 ∧ T.map π.toEmbedding ⊆ Three.supp e) ∨
        ∃ O, IsOctad16 G O ∧ ∃ e ∈ E, wt e = 8 ∧ Three.supp e = O.map π.toEmbedding

namespace CB48

/-! ## Bit masks and words -/

/-- The coordinates `j < 16` with bit `j` of `m` set. -/
def maskSet (m : ℕ) : Finset (Fin 16) :=
  univ.filter fun j => m.testBit j.val = true

/-- The binary word with support `maskSet m`. -/
def toVec2 (m : ℕ) : Fin 16 → ZMod 2 :=
  fun j => bif m.testBit j.val then 1 else 0

/-- The element `a + b ω` of `𝔽₄` for bits `a, b`. -/
def dec : Bool → Bool → F4
  | false, false => 0
  | true, false => 1
  | false, true => F4.w
  | true, true => F4.wb

/-- The word of `𝔽₄¹⁶` with planes `a, b`. -/
def toV (a b : ℕ) : Fin 16 → F4 :=
  fun j => dec (a.testBit j.val) (b.testBit j.val)

/-- The scalar with code `c`: `0, 1, ω, ω̄`. -/
def enc : ℕ → F4
  | 0 => 0
  | 1 => 1
  | 2 => F4.w
  | _ => F4.wb

theorem dec_xor : ∀ x y x' y' : Bool, dec (x ^^ x') (y ^^ y') = dec x y + dec x' y' := by decide

theorem toV_xor (a b a' b' : ℕ) : toV (a ^^^ a') (b ^^^ b') = toV a b + toV a' b' := by
  funext j
  simp only [toV, Nat.testBit_xor, Pi.add_apply]
  exact dec_xor _ _ _ _

theorem toV_zero : toV 0 0 = 0 := by
  funext j
  simp only [toV, Nat.zero_testBit, Pi.zero_apply]
  rfl

/-- Bit `j` of `mulA c a b`. -/
def mA (c : ℕ) (x y : Bool) : Bool :=
  match c with
  | 0 => false
  | 1 => x
  | 2 => y
  | _ => x ^^ y

/-- Bit `j` of `mulB c a b`. -/
def mB (c : ℕ) (x y : Bool) : Bool :=
  match c with
  | 0 => false
  | 1 => y
  | 2 => x ^^ y
  | _ => x

theorem testBit_mulA (c a b j : ℕ) (hc : c < 4) : (mulA c a b).testBit j = mA c (a.testBit j) (b.testBit j) := by
  interval_cases c
  · simp [mulA, mA]
  · rfl
  · rfl
  · simp [mulA, mA, Nat.testBit_xor]

theorem testBit_mulB (c a b j : ℕ) (hc : c < 4) : (mulB c a b).testBit j = mB c (a.testBit j) (b.testBit j) := by
  interval_cases c
  · simp [mulB, mB]
  · rfl
  · simp [mulB, mB, Nat.testBit_xor]
  · rfl

theorem enc_mul_dec : ∀ c, c < 4 → ∀ x y : Bool, enc c * dec x y = dec (mA c x y) (mB c x y) := by decide

theorem toV_mul (c : ℕ) (hc : c < 4) (a b : ℕ) : enc c • toV a b = toV (mulA c a b) (mulB c a b) := by
  funext j
  simp only [toV, Pi.smul_apply, smul_eq_mul, testBit_mulA c a b _ hc, testBit_mulB c a b _ hc]
  exact enc_mul_dec c hc _ _

theorem enc_surj : ∀ y : F4, ∃ c, c < 4 ∧ enc c = y := by decide

theorem dec_ne_zero : ∀ x y : Bool, dec x y ≠ 0 ↔ (x || y) = true := by decide

theorem supp_toV (a b : ℕ) : Three.supp (toV a b) = maskSet (a ||| b) := by
  ext j
  simp only [Three.mem_supp, toV, maskSet, mem_filter, mem_univ, true_and, Nat.testBit_or]
  exact dec_ne_zero _ _

theorem supp_toVec2 (m : ℕ) : Three.supp (toVec2 m) = maskSet m := by
  ext j
  simp only [Three.mem_supp, toVec2, maskSet, mem_filter, mem_univ, true_and]
  cases m.testBit j.val <;> decide

theorem card_maskSet (s : ℕ) : #(maskSet s) = wt16 s := by
  rw [maskSet, card_filter, Fin.sum_univ_eq_sum_range (fun j => if s.testBit j = true then 1 else 0) 16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, wt16, bitv, Bool.cond_eq_ite]

theorem wt_toV (a b : ℕ) : wt (toV a b) = wt16 (a ||| b) := by
  rw [← Three.card_supp, supp_toV, card_maskSet]

theorem testBit_false_of_lt {m i : ℕ} (hm : m < 65536) (hi : 16 ≤ i) : m.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  have h : (2 : ℕ) ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  calc m < 65536 := hm
    _ = 2 ^ 16 := by norm_num
    _ ≤ 2 ^ i := h

theorem and_eq_of_maskSet_subset {t s : ℕ} (ht : t < 65536) (h : maskSet t ⊆ maskSet s) : t &&& s = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 16
  · cases htb : t.testBit i
    · rfl
    · have hmem : (⟨i, hi⟩ : Fin 16) ∈ maskSet t := by simp [maskSet, htb]
      have hs := h hmem
      simp only [maskSet, mem_filter, mem_univ, true_and] at hs
      simp [hs]
  · rw [testBit_false_of_lt ht (by omega)]
    rfl

theorem eq_of_maskSet_eq {s o : ℕ} (hs : s < 65536) (ho : o < 65536) (h : maskSet s = maskSet o) : s = o := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · have h1 : (⟨i, hi⟩ : Fin 16) ∈ maskSet s ↔ (⟨i, hi⟩ : Fin 16) ∈ maskSet o := by rw [h]
    simp only [maskSet, mem_filter, mem_univ, true_and] at h1
    cases hsb : s.testBit i <;> cases hob : o.testBit i <;> simp_all
  · rw [testBit_false_of_lt hs (by omega), testBit_false_of_lt ho (by omega)]

/-! ## Soundness of the check -/

/-- The property checked at a leaf of `go`. -/
def LeafProp (x : Fin 16 → F4) : Prop :=
  x = 0 ∨ (6 ≤ wt x ∧ (wt x = 6 → ∀ t ∈ tets, ¬ maskSet t ⊆ Three.supp x) ∧
    (wt x = 8 → ∀ o ∈ octs, Three.supp x ≠ maskSet o))

theorem tets_lt : ∀ t ∈ tets, t < 65536 := by decide +kernel
theorem octs_lt : ∀ o ∈ octs, o < 65536 := by decide +kernel

theorem leaf_sound {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : leafOK tets octs 6 a b = true) :
    LeafProp (toV a b) := by
  simp only [leafOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.ble_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  rcases h with h0 | ⟨⟨h6, h6t⟩, h8o⟩
  · left
    have hab := Nat.or_eq_zero_iff.1 h0
    rw [hab.1, hab.2, toV_zero]
  · right
    have hs : a ||| b < 65536 := Nat.or_lt_two_pow (n := 16) ha hb
    rw [wt_toV, supp_toV]
    refine ⟨h6, fun hw t ht hsub => ?_, fun hw o ho heq => ?_⟩
    · rcases h6t with h6t | h6t
      · exact h6t hw
      · exact h6t t ht (and_eq_of_maskSet_subset (tets_lt t ht) hsub)
    · rcases h8o with h8o | h8o
      · exact h8o hw
      · exact h8o o ho (eq_of_maskSet_eq (octs_lt o ho) hs heq.symm)

theorem rowA_lt : ∀ r, rowA r < 65536 := by
  intro r
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> simp [rowA]

theorem rowB_lt : ∀ r, rowB r < 65536 := by
  intro r
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> simp [rowB]

theorem mulA_lt (c a b : ℕ) (ha : a < 65536) (hb : b < 65536) : mulA c a b < 65536 := by
  unfold mulA
  split
  · norm_num
  · exact ha
  · exact hb
  · exact Nat.xor_lt_two_pow (n := 16) ha hb

theorem mulB_lt (c a b : ℕ) (ha : a < 65536) (hb : b < 65536) : mulB c a b < 65536 := by
  unfold mulB
  split
  · norm_num
  · exact hb
  · exact Nat.xor_lt_two_pow (n := 16) ha hb
  · exact ha

/-- **Soundness of `go`:** if the check passes, every word `x + Σ_{i<n} c_i · row (r + i)` has the leaf property. -/
theorem go_sound : ∀ (n r a b : ℕ), a < 65536 → b < 65536 → go tets octs 6 n r a b = true →
    ∀ c : Fin n → F4, LeafProp (toV a b + ∑ i : Fin n, c i • toV (rowA (r + i)) (rowB (r + i))) := by
  intro n
  induction n with
  | zero =>
    intro r a b ha hb h c
    rw [Fin.sum_univ_zero, add_zero]
    exact leaf_sound ha hb h
  | succ n ih =>
    intro r a b ha hb h c
    obtain ⟨c0, hc0, hc0e⟩ := enc_surj (c 0)
    have hgo : go tets octs 6 n (r + 1) (a ^^^ mulA c0 (rowA r) (rowB r)) (b ^^^ mulB c0 (rowA r) (rowB r)) =
        true := by
      have h' : ([0, 1, 2, 3] : List ℕ).all (fun c => go tets octs 6 n (r + 1) (a ^^^ mulA c (rowA r) (rowB r))
          (b ^^^ mulB c (rowA r) (rowB r))) = true := h
      rw [List.all_eq_true] at h'
      apply h'
      interval_cases c0 <;> simp
    have hA : a ^^^ mulA c0 (rowA r) (rowB r) < 65536 :=
      Nat.xor_lt_two_pow (n := 16) ha (mulA_lt c0 _ _ (rowA_lt r) (rowB_lt r))
    have hB : b ^^^ mulB c0 (rowA r) (rowB r) < 65536 :=
      Nat.xor_lt_two_pow (n := 16) hb (mulB_lt c0 _ _ (rowA_lt r) (rowB_lt r))
    have key := ih (r + 1) _ _ hA hB hgo (fun i => c i.succ)
    have e1 : toV (a ^^^ mulA c0 (rowA r) (rowB r)) (b ^^^ mulB c0 (rowA r) (rowB r)) =
        toV a b + c 0 • toV (rowA r) (rowB r) := by
      rw [toV_xor, ← toV_mul c0 hc0, hc0e]
    have e2 : ∀ i : Fin n, toV (rowA (r + 1 + i)) (rowB (r + 1 + i)) =
        toV (rowA (r + (i.succ : ℕ))) (rowB (r + (i.succ : ℕ))) := by
      intro i
      rw [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    rw [e1] at key
    simp only [e2] at key
    rw [Fin.sum_univ_succ, ← add_assoc]
    simpa only [Fin.val_zero, Nat.add_zero] using key

/-! ## The code `E48` -/

/-- The code `E` of the length-48 test over `𝔽₄` (16 coordinates): the span of the systematic rows `erow`. -/
def E48 : Submodule F4 (Fin 16 → F4) :=
  Submodule.span F4 (Set.range erow)

theorem erow_toV : ∀ r : Fin 8, erow r = toV (rowA r) (rowB r) := by decide +kernel

/-- Every word of `E48` has the leaf property. -/
theorem E48_leaf {x : Fin 16 → F4} (hx : x ∈ E48) : LeafProp x := by
  rw [E48, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have h := go_sound 8 0 0 0 (by norm_num) (by norm_num) go_all c
  have e : ∀ i : Fin 8, toV (rowA (i : ℕ)) (rowB (i : ℕ)) = erow i := fun i => (erow_toV i).symm
  simp only [toV_zero, zero_add, e] at h
  exact h

theorem E48_minWt : ∀ e ∈ E48, e ≠ 0 → 6 ≤ wt e := by
  intro e he hne
  rcases E48_leaf he with h0 | ⟨h6, _⟩
  · exact absurd h0 hne
  · exact h6

theorem wt_erow1 : wt (erow 1) = 6 := by decide +kernel

theorem erow_hform : ∀ r s : Fin 8, F4.hform (erow r) (erow s) = 0 := by decide +kernel

theorem erow_unit : ∀ i j : Fin 8, erow j (Fin.castAdd 8 i) = if j = i then 1 else 0 := by decide +kernel

theorem single_hform : ∀ i j : Fin 8,
    F4.hform (Pi.single (Fin.castAdd 8 i) (1 : F4)) (erow j) = if j = i then 1 else 0 := by
  decide +kernel

theorem E48_le_hdual : E48 ≤ F4.hdual E48 := by
  rw [E48, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  rw [SetLike.mem_coe, F4.mem_hdual_span]
  rintro _ ⟨s, rfl⟩
  exact erow_hform r s

theorem erow_linearIndependent : LinearIndependent F4 erow := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (Fin.castAdd 8 i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, erow_unit, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at h
  exact h

theorem finrank_E48 : finrank F4 E48 = 8 := by
  rw [E48, finrank_span_eq_card erow_linearIndependent, Fintype.card_fin]

/-- The parity-check map `x ↦ (⟨x, erow i⟩)_i`; its kernel is the Hermitian dual of `E48`. -/
def checkMap : (Fin 16 → F4) →ₗ[F4] (Fin 8 → F4) where
  toFun x i := F4.hform x (erow i)
  map_add' x y := by
    funext i
    exact F4.hform_add_left x y (erow i)
  map_smul' a x := by
    funext i
    exact F4.hform_smul_left a x (erow i)

theorem ker_checkMap : LinearMap.ker checkMap = F4.hdual E48 := by
  ext x
  rw [LinearMap.mem_ker, E48, F4.mem_hdual_span]
  constructor
  · rintro h _ ⟨i, rfl⟩
    exact congrFun h i
  · intro h
    funext i
    exact h _ ⟨i, rfl⟩

theorem checkMap_surjective : Function.Surjective checkMap := by
  intro v
  refine ⟨∑ i : Fin 8, v i • Pi.single (Fin.castAdd 8 i) (1 : F4), ?_⟩
  rw [map_sum]
  funext j
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ i, checkMap (Pi.single (Fin.castAdd 8 i) (1 : F4)) j = if j = i then 1 else 0 :=
    fun i => single_hform i j
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finrank_hdual_E48 : finrank F4 (F4.hdual E48) = 8 := by
  have h := LinearMap.finrank_range_add_finrank_ker checkMap
  rw [LinearMap.range_eq_top.2 checkMap_surjective, finrank_top, ker_checkMap, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  omega

/-- `E48` is Hermitian self-dual (`x̄ = x²`). -/
theorem E48_hselfDual : F4.HSelfDual E48 :=
  Submodule.eq_of_le_of_finrank_le E48_le_hdual (by rw [finrank_hdual_E48, finrank_E48])

/-- The rows of the program's generator matrix lie in `E48` (they span it: rank 8). -/
theorem origRow_mem : ∀ r : Fin 8, origRow r ∈ E48 := by
  have h : ∀ r s : Fin 8, F4.hform (origRow r) (erow s) = 0 := by decide +kernel
  intro r
  rw [E48_hselfDual, E48, F4.mem_hdual_span]
  rintro _ ⟨s, rfl⟩
  exact h r s

/-! ## The labelling and `e8 ⊕ e8` -/

/-- The labelling `π` of `e8 ⊕ e8` (`piTab`): it maps `e8 ⊕ e8` onto the code `D` of the length-48 test. -/
def piCB : Equiv.Perm (Fin 16) where
  toFun i := ⟨piTab.getD i.val 0 % 16, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨piInvTab.getD i.val 0 % 16, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by decide
  right_inv := by decide

theorem supp_permute (π : Equiv.Perm (Fin 16)) (x : Fin 16 → ZMod 2) :
    Three.supp (permute π x) = (Three.supp x).map π.toEmbedding := by
  ext j
  simp only [Three.mem_supp, permute_apply, mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨π.symm j, h, Equiv.apply_symm_apply π j⟩
  · rintro ⟨i, hi, rfl⟩
    rwa [Equiv.symm_apply_apply]

theorem e8_mem_wordVec {y : Fin 8 → ZMod 2} (hy : y ∈ C72.Tests.e8) :
    ∃ Sx ∈ T3.e8Words, T3.wordVec Sx = y := by
  obtain ⟨a, b, c, d, rfl⟩ := C72.Tests.mem_e8_iff.1 hy
  clear hy
  revert a b c d
  decide +kernel

theorem cat_halves (x : Fin 16 → ZMod 2) :
    T3.cat (fun k : Fin 8 => x (Fin.castAdd 8 k)) (fun k : Fin 8 => x (Fin.natAdd 8 k)) = x := by
  funext i
  by_cases h : i.val < 8
  · have e : i = Fin.castAdd 8 ⟨i.val, h⟩ := Fin.ext rfl
    rw [e, T3.cat_castAdd]
  · have e : i = Fin.natAdd 8 (⟨i.val - 8, by omega⟩ : Fin 8) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rw [e, T3.cat_natAdd]

theorem e8e8_eq_cat {x : Fin 16 → ZMod 2} (hx : x ∈ T3.e8e8) :
    ∃ Sx ∈ T3.e8Words, ∃ Sx' ∈ T3.e8Words, T3.cat (T3.wordVec Sx) (T3.wordVec Sx') = x := by
  rw [T3.mem_e8e8] at hx
  obtain ⟨Sx, hSx, h1⟩ := e8_mem_wordVec hx.1
  obtain ⟨Sx', hSx', h2⟩ := e8_mem_wordVec hx.2
  exact ⟨Sx, hSx, Sx', hSx', by rw [h1, h2, cat_halves]⟩

theorem tet_check : ∀ Sx ∈ T3.e8Words, ∀ Sx' ∈ T3.e8Words,
    wt (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = 4 →
      ∃ t ∈ tets, permute piCB (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = toVec2 t := by
  decide +kernel

theorem oct_check : ∀ Sx ∈ T3.e8Words, ∀ Sx' ∈ T3.e8Words,
    wt (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = 8 →
      ∃ o ∈ octs, permute piCB (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = toVec2 o := by
  decide +kernel

/-- Without the labelling, `tetsStd` and `octsStd` are the tetrads and octads of `e8 ⊕ e8` (for control C01). -/
theorem tetStd_check : ∀ Sx ∈ T3.e8Words, ∀ Sx' ∈ T3.e8Words,
    wt (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = 4 →
      ∃ t ∈ tetsStd, T3.cat (T3.wordVec Sx) (T3.wordVec Sx') = toVec2 t := by
  decide +kernel

theorem octStd_check : ∀ Sx ∈ T3.e8Words, ∀ Sx' ∈ T3.e8Words,
    wt (T3.cat (T3.wordVec Sx) (T3.wordVec Sx')) = 8 →
      ∃ o ∈ octsStd, T3.cat (T3.wordVec Sx) (T3.wordVec Sx') = toVec2 o := by
  decide +kernel

theorem tet_of_isTetrad {T : Finset (Fin 16)} (hT : IsTetrad16 T3.e8e8 T) :
    ∃ t ∈ tets, maskSet t = T.map piCB.toEmbedding := by
  obtain ⟨x, hx, hw, rfl⟩ := hT
  obtain ⟨Sx, hSx, Sx', hSx', hcat⟩ := e8e8_eq_cat hx
  obtain ⟨t, ht, heq⟩ := tet_check Sx hSx Sx' hSx' (by rw [hcat]; exact hw)
  refine ⟨t, ht, ?_⟩
  rw [← supp_toVec2, ← heq, hcat, supp_permute]

theorem oct_of_isOctad {O : Finset (Fin 16)} (hO : IsOctad16 T3.e8e8 O) :
    ∃ o ∈ octs, maskSet o = O.map piCB.toEmbedding := by
  obtain ⟨x, hx, hw, rfl⟩ := hO
  obtain ⟨Sx, hSx, Sx', hSx', hcat⟩ := e8e8_eq_cat hx
  obtain ⟨o, ho, heq⟩ := oct_check Sx hSx Sx' hSx' (by rw [hcat]; exact hw)
  refine ⟨o, ho, ?_⟩
  rw [← supp_toVec2, ← heq, hcat, supp_permute]

end CB48

open CB48

/-- **For `H_CB`:** the length-48 analog of `H_CB` is false. The code `E48` (from the extended quadratic
residue code of length 48) and the labelling `piCB` of `e8 ⊕ e8` meet no forbidden configuration. -/
theorem not_H_CB48 : ¬ H_CB48 := by
  intro h
  rcases h E48 E48_hselfDual E48_minWt ⟨erow 1, Submodule.subset_span ⟨1, rfl⟩, wt_erow1⟩ T3.e8e8
      (Set.mem_insert _ _) piCB with ⟨T, hT, e, he, hw, hsub⟩ | ⟨O, hO, e, he, hw, hsupp⟩
  · obtain ⟨t, ht, hteq⟩ := tet_of_isTetrad hT
    rcases E48_leaf he with h0 | ⟨_, h6, _⟩
    · rw [h0, Three.wt_zero] at hw
      exact absurd hw (by norm_num)
    · exact h6 hw t ht (hteq ▸ hsub)
  · obtain ⟨o, ho, hoeq⟩ := oct_of_isOctad hO
    rcases E48_leaf he with h0 | ⟨_, _, h8⟩
    · rw [h0, Three.wt_zero] at hw
      exact absurd hw (by norm_num)
    · exact h8 hw o ho (hsupp.trans hoeq.symm)

end C72.T5
