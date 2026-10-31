import C72T5.CB48Data

/-!
# T5: the kernel check behind the length-48 analog of `H_CB` (core Lean only)

A word of `F4¹⁶` is stored as two bit planes `a, b` (coordinate `j` is `a_j + b_j ω`, `ω² = ω + 1`); addition is the
exclusive or of the planes, and `mulA c`, `mulB c` give the planes of `c · x` for the scalar with code `c`
(`0`, `1`, `2 = ω`, `3 = ω̄`). `go tl ol d n r a b` runs through all `4ⁿ` words `x + Σ_{i<n} c_i · row (r + i)` (`x` with
planes `a, b`) and checks `leafOK tl ol d`: the word is zero, or it has weight at least `d`, no mask of `tl` inside its
support if its weight is 6, and its support is no mask of `ol` if its weight is 8.

The four theorems `go_c0_*` evaluate the check for the systematic rows of `E` (`rowA`, `rowB`), the moved tetrads and
octads of `e8 ⊕ e8` (`tets`, `octs`) and `d = 6`, one declaration for each value of the first coefficient. The
soundness proof and the link with the code `E48` are in `C72T5.CB48`.
-/

namespace C72.T5.CB48

/-- Plane `a` of `c · x` for the scalar with code `c` and `x` with planes `a, b`: `ω (a + b ω) = b + (a + b) ω`,
`ω̄ (a + b ω) = (a + b) + a ω`. -/
def mulA (c a b : Nat) : Nat :=
  match c with
  | 0 => 0
  | 1 => a
  | 2 => b
  | _ => a ^^^ b

/-- Plane `b` of `c · x`. -/
def mulB (c a b : Nat) : Nat :=
  match c with
  | 0 => 0
  | 1 => b
  | 2 => a ^^^ b
  | _ => a

/-- Bit `i` of `s`, as `0` or `1`. -/
def bitv (s i : Nat) : Nat :=
  bif s.testBit i then 1 else 0

/-- The number of set bits of `s` among the bits `0, …, 15`. -/
def wt16 (s : Nat) : Nat :=
  bitv s 0 + bitv s 1 + bitv s 2 + bitv s 3 + bitv s 4 + bitv s 5 + bitv s 6 + bitv s 7 + bitv s 8 +
    bitv s 9 + bitv s 10 + bitv s 11 + bitv s 12 + bitv s 13 + bitv s 14 + bitv s 15

/-- The leaf condition for the word with planes `a, b` (support mask `a ||| b`). -/
def leafOK (tl ol : List Nat) (d a b : Nat) : Bool :=
  (a ||| b == 0) || (Nat.ble d (wt16 (a ||| b)) &&
    (wt16 (a ||| b) != 6 || tl.all fun t => t &&& (a ||| b) != t) &&
    (wt16 (a ||| b) != 8 || ol.all fun o => o != a ||| b))

/-- All words `x + Σ_{i<n} c_i · row (r + i)`, `x` with planes `a, b`, pass `leafOK tl ol d`. -/
def go (tl ol : List Nat) (d : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, a, b => leafOK tl ol d a b
  | n + 1, r, a, b => [0, 1, 2, 3].all fun c =>
      go tl ol d n (r + 1) (a ^^^ mulA c (rowA r) (rowB r)) (b ^^^ mulB c (rowA r) (rowB r))

theorem go_c0_0 : go tets octs 6 7 (0 + 1) (0 ^^^ mulA 0 (rowA 0) (rowB 0)) (0 ^^^ mulB 0 (rowA 0) (rowB 0)) = true := by
  decide +kernel

theorem go_c0_1 : go tets octs 6 7 (0 + 1) (0 ^^^ mulA 1 (rowA 0) (rowB 0)) (0 ^^^ mulB 1 (rowA 0) (rowB 0)) = true := by
  decide +kernel

theorem go_c0_2 : go tets octs 6 7 (0 + 1) (0 ^^^ mulA 2 (rowA 0) (rowB 0)) (0 ^^^ mulB 2 (rowA 0) (rowB 0)) = true := by
  decide +kernel

theorem go_c0_3 : go tets octs 6 7 (0 + 1) (0 ^^^ mulA 3 (rowA 0) (rowB 0)) (0 ^^^ mulB 3 (rowA 0) (rowB 0)) = true := by
  decide +kernel

/-- The whole check: all `4⁸` words of `E` pass. -/
theorem go_all : go tets octs 6 8 0 0 0 = true := by
  show ([0, 1, 2, 3] : List Nat).all (fun c => go tets octs 6 7 (0 + 1) (0 ^^^ mulA c (rowA 0) (rowB 0))
    (0 ^^^ mulB c (rowA 0) (rowB 0))) = true
  simp only [List.all_cons, List.all_nil, go_c0_0, go_c0_1, go_c0_2, go_c0_3, Bool.and_self]

end C72.T5.CB48
