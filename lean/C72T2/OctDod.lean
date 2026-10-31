import C72T2.OctDodData

/-!
# T2: the octads and dodecads of `G24` are those of the labelling programs

The point-placement search reads its octads and dodecads from `octdod.txt` (`octMasks`, `dodMasks` in
`C72T2.OctDodData`, generated from that file). Here, by kernel evaluation:

* `words 12 echelonMask 0` lists the `2¹² = 4096` words spanned by a reduced echelon basis of `G24`
  (`span_echelon`: that basis spans `G24`; `mem_G24_iff_words`);
* the words of weight 8 in this list are exactly `octMasks`, in the same order (`words_filter_octads`), and the words
  of weight 12 are exactly `dodMasks` (`words_filter_dodecads`).

Hence `IsOctad O ↔ O` is listed in `octdod.txt` (`isOctad_iff`) and `IsDodecad D ↔ D` is listed
(`isDodecad_iff`): the octads and dodecads in `H_CB` are the program's. The lists are strictly increasing
(`octMasks_sorted`, `dodMasks_sorted`), so they have no repetition, and have 759 and 2576 entries.
-/

namespace C72.Three

open Finset

/-- All `2ᵏ` words `acc ⊕ ⨁_{c_j = 1} ms_j` (bit masks), with `ms 0` as the most significant choice. -/
def words : (k : ℕ) → (Fin k → ℕ) → ℕ → List ℕ
  | 0, _, acc => [acc]
  | k + 1, ms, acc => words k (Fin.tail ms) acc ++ words k (Fin.tail ms) (acc ^^^ ms 0)

/-- Every listed word is a combination of the `ms j`. -/
theorem mem_words : ∀ (k : ℕ) (ms : Fin k → ℕ) (acc m : ℕ), m ∈ words k ms acc →
    ∃ c : Fin k → ZMod 2, toVec m = toVec acc + ∑ j, c j • toVec (ms j) := by
  intro k
  induction k with
  | zero =>
    intro ms acc m h
    rw [words, List.mem_singleton] at h
    subst h
    exact ⟨0, by simp⟩
  | succ k ih =>
    intro ms acc m h
    rw [words, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨c, hc⟩ := ih (Fin.tail ms) acc m h
      simp only [Fin.tail] at hc
      refine ⟨Fin.cons 0 c, ?_⟩
      rw [hc, Fin.sum_univ_succ]
      simp
    · obtain ⟨c, hc⟩ := ih (Fin.tail ms) (acc ^^^ ms 0) m h
      simp only [Fin.tail] at hc
      refine ⟨Fin.cons 1 c, ?_⟩
      rw [hc, Fin.sum_univ_succ, toVec_xor]
      simp [add_assoc]

/-- Every combination of the `ms j` is listed. -/
theorem words_complete : ∀ (k : ℕ) (ms : Fin k → ℕ) (acc : ℕ) (c : Fin k → ZMod 2),
    ∃ m ∈ words k ms acc, toVec m = toVec acc + ∑ j, c j • toVec (ms j) := by
  intro k
  induction k with
  | zero =>
    intro ms acc c
    exact ⟨acc, by simp [words], by simp⟩
  | succ k ih =>
    intro ms acc c
    rw [Fin.sum_univ_succ]
    rcases zmod2_cases (c 0) with h0 | h1
    · obtain ⟨m, hm, hmc⟩ := ih (Fin.tail ms) acc (Fin.tail c)
      simp only [Fin.tail] at hmc
      refine ⟨m, ?_, ?_⟩
      · rw [words, List.mem_append]
        exact Or.inl hm
      · rw [hmc, h0, zero_smul, zero_add]
    · obtain ⟨m, hm, hmc⟩ := ih (Fin.tail ms) (acc ^^^ ms 0) (Fin.tail c)
      simp only [Fin.tail] at hmc
      refine ⟨m, ?_, ?_⟩
      · rw [words, List.mem_append]
        exact Or.inr hm
      · rw [hmc, h1, one_smul, toVec_xor, add_assoc]

/-! ## Kernel checks -/

/-- The echelon basis lies in `G24` (it is orthogonal to the generators). -/
theorem echelon_orth : ∀ i j : Fin 12, toVec (echelonMask i) ⬝ᵥ g24gen j = 0 := by
  decide +kernel

/-- The generators of `G24` are among the words of the echelon basis. -/
theorem g24mask_mem_words : ∀ s : Fin 12, g24mask s ∈ words 12 echelonMask 0 := by
  decide +kernel

/-- **Octads**: the words of weight 8 of `G24`, listed by the echelon basis, are exactly `octdod.txt` line 1. -/
theorem words_filter_octads : (words 12 echelonMask 0).filter (fun m => wt (toVec m) == 8) = octMasks := by
  decide +kernel

/-- **Dodecads**: the words of weight 12 are exactly `octdod.txt` line 2. -/
theorem words_filter_dodecads :
    (words 12 echelonMask 0).filter (fun m => wt (toVec m) == 12) = dodMasks := by
  decide +kernel

theorem octMasks_length : octMasks.length = 759 := by
  decide +kernel

theorem dodMasks_length : dodMasks.length = 2576 := by
  decide +kernel

theorem octMasks_sorted : octMasks.IsChain (· < ·) := by
  decide +kernel

theorem dodMasks_sorted : dodMasks.IsChain (· < ·) := by
  decide +kernel

theorem octMasks_nodup : octMasks.Nodup :=
  (List.isChain_iff_pairwise.1 octMasks_sorted).imp ne_of_lt

theorem dodMasks_nodup : dodMasks.Nodup :=
  (List.isChain_iff_pairwise.1 dodMasks_sorted).imp ne_of_lt

/-! ## Consequences -/

/-- The echelon basis spans `G24`. -/
theorem span_echelon : Submodule.span (ZMod 2) (Set.range fun j => toVec (echelonMask j)) = G24 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_G24_of_orth (echelon_orth i)
  · rw [G24, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := mem_words 12 echelonMask 0 (g24mask s) (g24mask_mem_words s)
    rw [SetLike.mem_coe, g24gen, hc, toVec_zero, zero_add]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- The words of `G24` are the words listed by `words 12 echelonMask 0`. -/
theorem mem_G24_iff_words {x : Fin 24 → ZMod 2} : x ∈ G24 ↔ ∃ m ∈ words 12 echelonMask 0, toVec m = x := by
  constructor
  · intro hx
    rw [← span_echelon, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨m, hm, hmc⟩ := words_complete 12 echelonMask 0 c
    exact ⟨m, hm, by rw [hmc, toVec_zero, zero_add]⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨c, hc⟩ := mem_words 12 echelonMask 0 m hm
    rw [← span_echelon, hc, toVec_zero, zero_add]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- **The octads of `G24` are exactly the 759 octads of `octdod.txt`.** -/
theorem isOctad_iff {O : Finset (Fin 24)} : IsOctad O ↔ ∃ m ∈ octMasks, supp (toVec m) = O := by
  constructor
  · rintro ⟨x, hx, hx8, rfl⟩
    obtain ⟨m, hm, rfl⟩ := mem_G24_iff_words.1 hx
    refine ⟨m, ?_, rfl⟩
    rw [← words_filter_octads, List.mem_filter]
    exact ⟨hm, by simp [hx8]⟩
  · rintro ⟨m, hm, rfl⟩
    rw [← words_filter_octads, List.mem_filter] at hm
    refine ⟨toVec m, mem_G24_iff_words.2 ⟨m, hm.1, rfl⟩, ?_, rfl⟩
    simpa using hm.2

/-- **The dodecads of `G24` are exactly the 2576 dodecads of `octdod.txt`.** -/
theorem isDodecad_iff {D : Finset (Fin 24)} : IsDodecad D ↔ ∃ m ∈ dodMasks, supp (toVec m) = D := by
  constructor
  · rintro ⟨x, hx, hx12, rfl⟩
    obtain ⟨m, hm, rfl⟩ := mem_G24_iff_words.1 hx
    refine ⟨m, ?_, rfl⟩
    rw [← words_filter_dodecads, List.mem_filter]
    exact ⟨hm, by simp [hx12]⟩
  · rintro ⟨m, hm, rfl⟩
    rw [← words_filter_dodecads, List.mem_filter] at hm
    refine ⟨toVec m, mem_G24_iff_words.2 ⟨m, hm.1, rfl⟩, ?_, rfl⟩
    simpa using hm.2

end C72.Three
