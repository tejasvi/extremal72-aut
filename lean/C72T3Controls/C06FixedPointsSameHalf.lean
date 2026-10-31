import C72T3.E8

/-!
# Control C06 (must not build): in `e8 ⊕ e8` no word of weight 4 contains both fixed-point coordinates

Lemma 2.1 uses that in `e8 ⊕ e8` exactly the pairs inside one component lie in a word of weight 4
(`C72.T3.e8e8_pair`, `C72.T3.halves_differ`), while in `d₁₆⁺` every pair does (`C72.T3.d16plus_pair`). The claim
that some word of `e8 ⊕ e8` of weight 4 contains the coordinates 7 and 15 (one in each half) must fail.
Expected failure: `decide` proves that the existence statement below is false.
-/

open C72 C72.T3

theorem C72.T3.Controls.c06_fixed_points_same_word :
    ∃ Sx ∈ e8Words, ∃ Sx' ∈ e8Words, wt (cat (wordVec Sx) (wordVec Sx')) = 4 ∧
      cat (wordVec Sx) (wordVec Sx') 7 = 1 ∧ cat (wordVec Sx) (wordVec Sx') 15 = 1 := by
  decide +kernel
