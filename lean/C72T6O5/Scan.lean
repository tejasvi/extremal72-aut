import C72T6O5.Key
import C72T3.Tests

/-!
# T6 (order 5): the scan of the nonzero entries and the normalisation of a joining entry (Sec. 2.4)

* The rows are processed in the order `0, 1, 3, 2, 4, 5, 6`: the row at depth `d` is `rowAt d`, and `depth` is the
  inverse (`depth_rowAt`). The entries are scanned row by row in order of depth, and within a row in order of column:
  entry `(i, j)` is the `scanIdx i j`-th position (`scanIdx_inj`, `scanIdx_lt`).
* Each scanned (nonzero) entry `(a, b)` is an edge between the row vertex `Sum.inl a` and the column vertex
  `Sum.inr b`. `earlierEdge U i j` is the graph built from the entries scanned before `(i, j)`, and the components are
  the classes of its equivalence closure `Relation.EqvGen`. Entry `(i, j)` joins two different components when its row
  and its column are not connected (`Joins`).
* Property (iii) of Lemma 2.5 (`NFiii`): every scanned entry that joins two different components is the representative
  `T3.Tests.clsRep` (`1`, `1 + t`, `1 + t²`) of its norm class.
* `normalise_joining`: a joining entry is normalised by (a) with `D₁ = D₂ = ζ ∈ μ₅` on the rows and columns of the
  component of its column and `1` elsewhere. This changes no earlier scanned entry and no class (so no zero entry, no
  pattern and no key), and the graphs are unchanged (`joins_congr`).
* `first_rep`, `row0_rep`: in a matrix with (iii), the first nonzero entry of each row, and every entry of the row at
  depth 0, is the representative of its class (the remark after Lemma 2.5).
-/

namespace C72.T6O5

open C72.T3 Finset Equiv Matrix

/-- The row at depth `d` (Sec. 2.4): the rows of `U` are processed in the order `0, 1, 3, 2, 4, 5, 6`. -/
def rowAt : Fin 7 → Fin 7 :=
  ![0, 1, 3, 2, 4, 5, 6]

/-- The depth of row `i`: `depth (rowAt d) = d` (`depth_rowAt`). -/
def depth (i : Fin 7) : ℕ :=
  if i = 2 then 3 else if i = 3 then 2 else i

theorem depth_rowAt : ∀ d : Fin 7, depth (rowAt d) = d := by decide +kernel

theorem rowAt_zero : rowAt 0 = 0 :=
  rfl

theorem depth_lt : ∀ i : Fin 7, depth i < 7 := by decide +kernel

theorem depth_injective : ∀ i i' : Fin 7, depth i = depth i' → i = i' := by decide +kernel

theorem depth_eq_zero : ∀ i : Fin 7, depth i = 0 ↔ i = 0 := by decide +kernel

/-- The position of entry `(i, j)` in the scan: row by row in order of depth, and within a row in order of column. -/
def scanIdx (i j : Fin 7) : ℕ :=
  7 * depth i + j

theorem scanIdx_lt (i j : Fin 7) : scanIdx i j < 49 := by
  have := depth_lt i
  have := j.isLt
  unfold scanIdx
  omega

theorem scanIdx_inj {i j i' j' : Fin 7} (h : scanIdx i j = scanIdx i' j') : i = i' ∧ j = j' := by
  unfold scanIdx at h
  have hj := j.isLt
  have hj' := j'.isLt
  have hd : depth i = depth i' := by omega
  exact ⟨depth_injective _ _ hd, Fin.ext (by omega)⟩

/-! ## The graph of the scanned entries -/

/-- The bipartite graph on the rows (`Sum.inl a`) and the columns (`Sum.inr b`) built from the nonzero entries of `U`
scanned before position `(i, j)`: entry `(a, b)` is the edge from `Sum.inl a` to `Sum.inr b`. -/
def earlierEdge (U : Matrix (Fin 7) (Fin 7) F16) (i j : Fin 7) (x y : Fin 7 ⊕ Fin 7) : Prop :=
  ∃ a b, U a b ≠ 0 ∧ scanIdx a b < scanIdx i j ∧ x = Sum.inl a ∧ y = Sum.inr b

/-- Entry `(i, j)` joins two different components of the graph built from the earlier entries: its row and its column
are not connected (the components are the classes of the equivalence closure `Relation.EqvGen`). -/
def Joins (U : Matrix (Fin 7) (Fin 7) F16) (i j : Fin 7) : Prop :=
  ¬ Relation.EqvGen (earlierEdge U i j) (Sum.inl i) (Sum.inr j)

/-- Property (iii) of Lemma 2.5: every scanned entry that joins two different components of the graph built from the
earlier entries is the representative `1`, `1 + t`, `1 + t²` of its norm class. -/
def NFiii (U : Matrix (Fin 7) (Fin 7) F16) : Prop :=
  ∀ i j, U i j ≠ 0 → Joins U i j → U i j = T3.Tests.clsRep (cls (U i j))

/-- The graphs depend only on which entries are zero. -/
theorem joins_congr {U V : Matrix (Fin 7) (Fin 7) F16} (h : ∀ a b, U a b = 0 ↔ V a b = 0) (i j : Fin 7) :
    Joins U i j ↔ Joins V i j := by
  have he : earlierEdge U i j = earlierEdge V i j := by
    funext x y
    apply propext
    simp only [earlierEdge, ne_eq, h]
  rw [Joins, Joins, he]

/-- In the equivalence closure of a relation, a vertex without edges is related only to itself. -/
theorem iff_of_eqvGen_of_isolated {α : Type*} {r : α → α → Prop} {x : α} (hx : ∀ y, ¬ r x y ∧ ¬ r y x) :
    ∀ a b, Relation.EqvGen r a b → (a = x ↔ b = x) := by
  intro a b h
  induction h with
  | rel a b hab =>
    have ha : a ≠ x := fun h => (hx b).1 (h ▸ hab)
    have hb : b ≠ x := fun h => (hx a).2 (h ▸ hab)
    exact ⟨fun h => absurd h ha, fun h => absurd h hb⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Normalising a joining entry -/

theorem rep_mul_inv_mu5 : ∀ y : F16, y ≠ 0 → (T3.Tests.clsRep (cls y) * y⁻¹) ^ 5 = 1 := by decide +kernel

/-- **The step of Lemma 2.5 (iii).** Let `(i, j)` be a nonzero entry that joins two different components of the graph
built from the earlier entries, and let `K` be the component of its column `j`. Apply (a) with `D₁ = D₂ = ζ ∈ μ₅` on the
rows and columns in `K` and `1` elsewhere. The row `i` is outside `K`, so the entry is multiplied by `ζ`, and a suitable
`ζ` makes it the representative of its class. An earlier scanned nonzero entry has both ends in `K` or both outside
(it is an edge of the graph), so it is multiplied by `ζ⁻¹ ζ = 1` or by `1`. No class changes. -/
theorem normalise_joining (U : Matrix (Fin 7) (Fin 7) F16) {i j : Fin 7} (hij : U i j ≠ 0) (hJ : Joins U i j) :
    ∃ d₁ d₂ : Fin 7 → F16, (∀ k, d₁ k ^ 5 = 1) ∧ (∀ k, d₂ k ^ 5 = 1) ∧
      ((diagonal d₁)⁻¹ * U * diagonal d₂) i j = T3.Tests.clsRep (cls (U i j)) ∧
      (∀ a b, U a b ≠ 0 → scanIdx a b < scanIdx i j → ((diagonal d₁)⁻¹ * U * diagonal d₂) a b = U a b) ∧
      (∀ a b, cls (((diagonal d₁)⁻¹ * U * diagonal d₂) a b) = cls (U a b)) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F16, ζ = T3.Tests.clsRep (cls (U i j)) * (U i j)⁻¹ := ⟨_, rfl⟩
  have hζ5 : ζ ^ 5 = 1 := hζ ▸ rep_mul_inv_mu5 _ hij
  obtain ⟨K, hK⟩ : ∃ K : Fin 7 ⊕ Fin 7 → Prop,
      K = fun x => Relation.EqvGen (earlierEdge U i j) x (Sum.inr j) := ⟨_, rfl⟩
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin 7 → F16, d = fun a => if K (Sum.inl a) then ζ else 1 := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin 7 → F16, d = fun b => if K (Sum.inr b) then ζ else 1 := ⟨_, rfl⟩
  have h₁ : ∀ k, d₁ k ^ 5 = 1 := fun k => by
    rw [hd₁]
    dsimp only
    split_ifs
    exacts [hζ5, one_pow 5]
  have h₂ : ∀ k, d₂ k ^ 5 = 1 := fun k => by
    rw [hd₂]
    dsimp only
    split_ifs
    exacts [hζ5, one_pow 5]
  refine ⟨d₁, d₂, h₁, h₂, ?_, ?_, ?_⟩
  · have hi : ¬ K (Sum.inl i) := by
      rw [hK]
      exact hJ
    have hj : K (Sum.inr j) := by
      rw [hK]
      exact Relation.EqvGen.refl _
    rw [scale_apply h₁, hd₁, hd₂]
    dsimp only
    rw [ite_eq_right hi, ite_eq_left hj, inv_one, one_mul, hζ]
    calc U i j * (T3.Tests.clsRep (cls (U i j)) * (U i j)⁻¹)
        = T3.Tests.clsRep (cls (U i j)) * (U i j * (U i j)⁻¹) := by ring
      _ = T3.Tests.clsRep (cls (U i j)) := by rw [mul_inv_cancel₀ hij, mul_one]
  · intro a b hab hlt
    have hedge : Relation.EqvGen (earlierEdge U i j) (Sum.inl a) (Sum.inr b) :=
      Relation.EqvGen.rel _ _ ⟨a, b, hab, hlt, rfl, rfl⟩
    have hiff : K (Sum.inl a) ↔ K (Sum.inr b) := by
      rw [hK]
      exact ⟨fun h => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hedge) h,
        fun h => Relation.EqvGen.trans _ _ _ hedge h⟩
    rw [scale_apply h₁, hd₁, hd₂]
    dsimp only
    by_cases ha : K (Sum.inl a)
    · rw [ite_eq_left ha, ite_eq_left (hiff.1 ha), mul_comm ζ⁻¹, mul_assoc, inv_mul_cancel₀ (mu5_ne_zero _ hζ5),
        mul_one]
    · rw [ite_eq_right ha, ite_eq_right (fun h => ha (hiff.2 h)), inv_one, one_mul, mul_one]
  · intro a b
    rw [scale_apply h₁]
    have e : (d₁ a)⁻¹ * U a b * d₂ b = U a b * ((d₁ a)⁻¹ * d₂ b) := by ring
    rw [e, cls_mul_mu5 _ _ (mu5_mul _ _ (mu5_inv _ (h₁ a)) (h₂ b))]

/-! ## Representatives forced by (iii) -/

theorem clsRep_cls_zero : T3.Tests.clsRep (cls 0) = 0 := by decide

/-- In a matrix with (iii), the first nonzero entry of each row is the representative of its class: its row vertex
has no earlier edge. -/
theorem first_rep {U : Matrix (Fin 7) (Fin 7) F16} (hU : NFiii U) {i j : Fin 7} (hij : U i j ≠ 0)
    (hfirst : ∀ b, b < j → U i b = 0) : U i j = T3.Tests.clsRep (cls (U i j)) := by
  apply hU i j hij
  intro h
  have hiso : ∀ y, ¬ earlierEdge U i j (Sum.inl i) y ∧ ¬ earlierEdge U i j y (Sum.inl i) := by
    intro y
    constructor
    · rintro ⟨a, b, hab, hlt, ha, -⟩
      cases ha
      apply hab
      apply hfirst
      show (b : ℕ) < j
      unfold scanIdx at hlt
      omega
    · rintro ⟨a, b, -, -, -, hb⟩
      exact Sum.inl_ne_inr hb
  exact Sum.inr_ne_inl ((iff_of_eqvGen_of_isolated hiso _ _ h).1 rfl)

/-- In a matrix with (iii), every entry of the row at depth 0 is the representative of its class: its column vertex
has no earlier edge. -/
theorem row0_rep {U : Matrix (Fin 7) (Fin 7) F16} (hU : NFiii U) (j : Fin 7) :
    U (rowAt 0) j = T3.Tests.clsRep (cls (U (rowAt 0) j)) := by
  by_cases hz : U (rowAt 0) j = 0
  · rw [hz, clsRep_cls_zero]
  apply hU _ j hz
  intro h
  have hiso : ∀ y, ¬ earlierEdge U (rowAt 0) j (Sum.inr j) y ∧ ¬ earlierEdge U (rowAt 0) j y (Sum.inr j) := by
    intro y
    constructor
    · rintro ⟨a, b, -, -, ha, -⟩
      exact Sum.inr_ne_inl ha
    · rintro ⟨a, b, -, hlt, -, hb⟩
      cases hb
      have h0 : depth (rowAt 0) = 0 := depth_rowAt 0
      unfold scanIdx at hlt
      omega
  exact Sum.inl_ne_inr ((iff_of_eqvGen_of_isolated hiso _ _ (Relation.EqvGen.symm _ _ h)).1 rfl)

end C72.T6O5
