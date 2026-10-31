import C72T6O5.Normal

/-!
# T6 (order 5): the rows at depth 0 of Table 1 and the normal form

T3 defines the seven rows at depth 0 of Table 1 (`T3.Tests.keyRow k`, the pattern `c₀ … c₆` of key `k`,
`T3.Tests.keyPattern k`, with each nonzero entry the representative of its class). Here:

* the pattern of each of them is its key (`keyRow_key`), so each listed pattern is the smallest in its orbit under the
  collineations and the Frobenius map, as Table 1 says; the seven keys are distinct (`keyRow_key_injective`). The
  check runs on the class vectors (`key_eq_keyC`, `keyC_keyPattern`);
* in normal form, a row at depth 0 whose key is the key of `keyRow k` is `keyRow k` (`row0_eq_keyRow`): the remark
  after Lemma 2.5 that the row at depth 0 is determined by its key. The paper's "seven keys occur" (Section 2.4)
  means the keys of the rows of the set `R` of Sec. 2.5. That exactly these seven keys occur among the rows of `R` is
  a computer enumeration, which is not formalized here.
-/

namespace C72.T6O5

open C72.T3

theorem cls_keyRow : ∀ k j : Fin 7, cls (T3.Tests.keyRow k j) = T3.Tests.keyPattern k j := by decide +kernel

theorem keyC_keyPattern : ∀ k : Fin 7, keyC (T3.Tests.keyPattern k) = patC (T3.Tests.keyPattern k) := by
  decide +kernel

/-- The pattern of each depth-0 row of Table 1 is its key. -/
theorem keyRow_key (k : Fin 7) : key (T3.Tests.keyRow k) = pattern (T3.Tests.keyRow k) := by
  have h : (fun j => cls (T3.Tests.keyRow k j)) = T3.Tests.keyPattern k := funext (cls_keyRow k)
  rw [key_eq_keyC, pattern_eq_patC, h, keyC_keyPattern]

theorem keyRow_key_injective : ∀ k k' : Fin 7, key (T3.Tests.keyRow k) = key (T3.Tests.keyRow k') → k = k' := by
  intro k k' h
  rw [keyRow_key, keyRow_key] at h
  revert k k'
  decide +kernel

theorem keyRow_rep : ∀ k j : Fin 7, T3.Tests.clsRep (cls (T3.Tests.keyRow k j)) = T3.Tests.keyRow k j := by
  decide +kernel

/-- In normal form, a row at depth 0 with the key of the depth-0 row `k` of Table 1 is that row. -/
theorem row0_eq_keyRow {V : Matrix (Fin 7) (Fin 7) F16} (hV : NormalForm V) (k : Fin 7)
    (h : key (V (rowAt 0)) = key (T3.Tests.keyRow k)) : V (rowAt 0) = T3.Tests.keyRow k := by
  have hVii : pattern (V (rowAt 0)) = key (V (rowAt 0)) := hV.2.1
  have hp : pattern (V (rowAt 0)) = pattern (T3.Tests.keyRow k) := by rw [hVii, h, keyRow_key]
  funext j
  rw [row0_rep hV.2.2 j, cls_eq_of_pattern_eq hp j, keyRow_rep]

end C72.T6O5
