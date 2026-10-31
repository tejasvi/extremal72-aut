/-!
# T3: the finite check behind Lemma 2.3 (core Lean only, evaluated by the kernel)

Lemma 2.3: no nonzero `v ∈ 𝔽₁₆⁷` with `⟨v, v⟩ = 0` satisfies `M(λv) ≥ 16` for all `λ ≠ 0`.

`M(λv)` depends only on the norm classes `c_i ∈ {0, 1, 2, 3}` of the entries of `v` (0 for a zero entry) and
on the class of `λ`. After the scaling `λ_r` that maps class `r` onto `μ₅`, an entry of class `c` has
`|ψ| = wr r c` (4 if `c = r`, 2 for another nonzero class, 0 for a zero entry). The isotropy
`⟨v, v⟩ = Σ_i N(v_i) = 0` says that the exclusive or of the class codes is 0, so `c₆` is determined by
`c₀, …, c₅`.

`chk d c₀` checks, for every `c₁, …, c₅ < 4` and `c₆ = c₀ ⊕ … ⊕ c₅`, that the pattern is zero or that some
scaling `r ∈ {1, 2, 3}` and some word `(S, x)` of `e8` give a term `< d`. The soundness proof and the link
with `M` are in `C72T3.L23`. This module imports nothing, so the kernel evaluates only the definitions below.
-/

namespace C72.T3.L23

/-- `|ψ(λ_r y)|` for an entry `y` of norm class `c` (`c = 0`: zero entry). -/
def wr (r c : Nat) : Nat :=
  bif c == 0 then 0 else bif c == r then 4 else 2

/-- One coordinate of the expression of Sec. 2.3: `5 - w` on `S`, `w` off `S`. -/
def tc (b : Bool) (w : Nat) : Nat :=
  bif b then 5 - w else w

/-- A word `(S, x)` of `e8` on one side: the membership bits of the points `0, …, 6` in `S`, and `x`. -/
structure Word where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  x : Nat

/-- The membership bit of the point `i`. -/
def Word.bit (q : Word) : Nat → Bool
  | 0 => q.b0
  | 1 => q.b1
  | 2 => q.b2
  | 3 => q.b3
  | 4 => q.b4
  | 5 => q.b5
  | 6 => q.b6
  | _ => false

/-- `x + Σ_{i ∈ S} (5 - w_i) + Σ_{i ∉ S} w_i`. -/
def term (q : Word) (w0 w1 w2 w3 w4 w5 w6 : Nat) : Nat :=
  q.x + tc q.b0 w0 + tc q.b1 w1 + tc q.b2 w2 + tc q.b3 w3 + tc q.b4 w4 + tc q.b5 w5 + tc q.b6 w6

/-- The 16 words of `e8`: `(∅, 0)`, `({0,…,6}, 1)`, and `(L, 1)`, `(Lᶜ, 0)` for the lines
`{0,1,3}`, `{1,2,4}`, `{2,3,5}`, `{3,4,6}`, `{4,5,0}`, `{5,6,1}`, `{6,0,2}`. -/
def words : List Word :=
  [⟨false, false, false, false, false, false, false, 0⟩,
   ⟨true, true, true, true, true, true, true, 1⟩,
   ⟨true, true, false, true, false, false, false, 1⟩,
   ⟨false, false, true, false, true, true, true, 0⟩,
   ⟨false, true, true, false, true, false, false, 1⟩,
   ⟨true, false, false, true, false, true, true, 0⟩,
   ⟨false, false, true, true, false, true, false, 1⟩,
   ⟨true, true, false, false, true, false, true, 0⟩,
   ⟨false, false, false, true, true, false, true, 1⟩,
   ⟨true, true, true, false, false, true, false, 0⟩,
   ⟨true, false, false, false, true, true, false, 1⟩,
   ⟨false, true, true, true, false, false, true, 0⟩,
   ⟨false, true, false, false, false, true, true, 1⟩,
   ⟨true, false, true, true, true, false, false, 0⟩,
   ⟨true, false, true, false, false, false, true, 1⟩,
   ⟨false, true, false, true, true, true, false, 0⟩]

/-- Some scaling `r ∈ {1, 2, 3}` gives a term `< d` for the word `q`. -/
def smallFor (d : Nat) (q : Word) (c0 c1 c2 c3 c4 c5 c6 : Nat) : Bool :=
  Nat.blt (term q (wr 1 c0) (wr 1 c1) (wr 1 c2) (wr 1 c3) (wr 1 c4) (wr 1 c5) (wr 1 c6)) d ||
    Nat.blt (term q (wr 2 c0) (wr 2 c1) (wr 2 c2) (wr 2 c3) (wr 2 c4) (wr 2 c5) (wr 2 c6)) d ||
    Nat.blt (term q (wr 3 c0) (wr 3 c1) (wr 3 c2) (wr 3 c3) (wr 3 c4) (wr 3 c5) (wr 3 c6)) d

/-- The pattern `(c₀, …, c₆)` is zero, or some scaling and some word give a term `< d`. -/
def okPat (d c0 c1 c2 c3 c4 c5 c6 : Nat) : Bool :=
  (c0 == 0 && c1 == 0 && c2 == 0 && c3 == 0 && c4 == 0 && c5 == 0 && c6 == 0) ||
    words.any fun q => smallFor d q c0 c1 c2 c3 c4 c5 c6

/-- The class codes. -/
def cs : List Nat :=
  [0, 1, 2, 3]

/-- All patterns with first entry `c₀` and `c₆ = c₀ ⊕ c₁ ⊕ … ⊕ c₅`. -/
def chk (d c0 : Nat) : Bool :=
  cs.all fun c1 => cs.all fun c2 => cs.all fun c3 => cs.all fun c4 => cs.all fun c5 =>
    okPat d c0 c1 c2 c3 c4 c5 (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ c5)

theorem chk16_0 : chk 16 0 = true := by decide +kernel
theorem chk16_1 : chk 16 1 = true := by decide +kernel
theorem chk16_2 : chk 16 2 = true := by decide +kernel
theorem chk16_3 : chk 16 3 = true := by decide +kernel

/-- The same check with threshold 12 returns `false`: the check is not vacuous. -/
theorem chk12_0 : chk 12 0 = false := by decide +kernel

end C72.T3.L23
