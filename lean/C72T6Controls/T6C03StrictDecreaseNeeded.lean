import C72T6.Refute

/-!
# Control T6C03 (must not build): Lemma 6.3 needs the strict decrease

With `K(B^g) ≤ K(B)` in place of `K(B^g) < K(B)` in the removal condition, Lemma 6.3 (`C72.T6.lemma63_abstract`) fails
(`C72.T6.Refute.lemma63_needs_strict`): for two solutions swapped by `g`, a constant key and one form per node, every node
may be removed. This is the conclusion of the weakened lemma for that model (solutions: all; `ext B n`: `B = n`;
removed: all).
Expected failure: `decide` proves that `∃ B, True ∧ ∀ n, B = n → ¬True` is false.
-/

theorem C72.Controls.t6c03_strict_decrease_needed : ∃ B : Bool, True ∧ ∀ n : Bool, B = n → ¬ True := by
  decide
