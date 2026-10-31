import C72T2.TheoremB
import C72T2.OctDod

/-!
# T2: `H_CB` with the program's octads and dodecads

By `isOctad_iff` and `isDodecad_iff`, the octads and dodecads of `G24` are the entries of `octdod.txt`. So `H_CB`
is equivalent to the same statement with "an octad `O` of `G24`" replaced by "a mask `m` on line 1 of
`octdod.txt`, `O = supp m`", and the same for dodecads and line 2 (`H_CB_iff_octdod`): this is the statement about
the program's own input.
-/

namespace C72

open Equiv Finset F4 Three

/-- `H_CB` stated with the octads and dodecads of `octdod.txt`. -/
theorem H_CB_iff_octdod : H_CB ↔
    ∀ E : Submodule F4 (Fin 24 → F4), HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) → (∃ e ∈ E, wt e = 8) →
      ∀ π : Perm (Fin 24),
        (∃ m ∈ octMasks, ∃ e ∈ E, (wt e = 8 ∧ 7 ≤ #((supp (toVec m)).map π.toEmbedding ∩ supp e)) ∨
            (wt e = 10 ∧ (supp (toVec m)).map π.toEmbedding ⊆ supp e)) ∨
          ∃ m ∈ dodMasks, ∃ e ∈ E, wt e = 12 ∧ supp e = (supp (toVec m)).map π.toEmbedding := by
  constructor
  · intro h E hE hE8 hEw π
    rcases h E hE hE8 hEw π with ⟨O, hO, hf⟩ | ⟨D, hD, hf⟩
    · obtain ⟨m, hm, rfl⟩ := isOctad_iff.1 hO
      exact Or.inl ⟨m, hm, hf⟩
    · obtain ⟨m, hm, rfl⟩ := isDodecad_iff.1 hD
      exact Or.inr ⟨m, hm, hf⟩
  · intro h E hE hE8 hEw π
    rcases h E hE hE8 hEw π with ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩
    · exact Or.inl ⟨_, isOctad_iff.2 ⟨m, hm, rfl⟩, hf⟩
    · exact Or.inr ⟨_, isDodecad_iff.2 ⟨m, hm, rfl⟩, hf⟩

end C72
