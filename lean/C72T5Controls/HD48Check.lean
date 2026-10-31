import C72T4.Codes36Check

/-!
# T5 controls: the kernel check behind the length-48 analog of `H_D` (core Lean only)

A word of length 24 is a bit mask (coordinate `i` is bit `i`). The data were computed by a script:
the extended quadratic residue code `C` of
length 48 (spanned by the shifts of the quadratic-residue word modulo 47; the image of the supplement's QR48 under
`x ↦ −x`), its fixed-point-free involution `x ↦ −1/x` of `P¹(𝔽₄₇)`, and the contracted fixed code `Y` (one
coordinate for each 2-cycle). `yrows` is a basis of `Y`, systematic on the coordinates `12, …, 23` (bit `12 + j'`
of row `j` is `[j = j']`). `zrows` gives for each row `y_j` a word `z_j` with `(z_j | z_j + y_j) ∈ C`, so that
`B(y, y') = ⟨z_y, y'⟩` is the form of T4's Definition 3.1 with `C = C_B`.

`go T n r a b` runs through all `2ⁿ` words `y = a + Σ_{i<n} c_i y_{r+i}`, together with `z = b + Σ_{i<n} c_i z_{r+i}`,
and checks `leafOK T`: `y = 0`, or `|y| ≥ 6` and, if `|y| < T`, no set `e` of coordinates outside `supp y` with
`2|e| < T − |y|` has `⟨𝟙_e, x⟩ = ⟨z, x⟩` for all words `x` of the list `elim y 24 yrows`. That list consists of words
of `Y` (sums of rows, obtained by elimination on the coordinates of `supp y`); the check verifies that they are
disjoint from `y`. `noE` runs through the sets `e`, on the packed syndrome (bit `k` is `⟨z, x_k⟩`) and the packed
columns (bit `k` of column `i` is coordinate `i` of `x_k`).

The four theorems `go_12_*` evaluate the check for `T = 12`, one declaration for each value of the first two
coefficients. The soundness proof and the statement are in `C72T5Controls.HD48`.
-/

namespace C72.T5.HD48

open C72.T4

/-- The basis rows `y_0, …, y_11` of `Y` (bit `12 + j'` of `y_j` is `[j = j']`). -/
def yrows : List Nat :=
  [6298, 11633, 17627, 36825, 68208, 133246, 265198, 526981, 1050306, 2100471, 4195814, 8392096]

/-- The words `z_0, …, z_11`: `(z_j | z_j + y_j)` lies in the code of length 48. -/
def zrows : List Nat :=
  [139482, 141552, 91353, 164553, 76704, 140782, 400301, 6726, 207810, 79990, 14774, 212016]

/-- Row `r` of `Y` (0 out of range). -/
def yrow (r : Nat) : Nat :=
  yrows.getD r 0

/-- The word `z_r` (0 out of range). -/
def zrow (r : Nat) : Nat :=
  zrows.getD r 0

/-- The number of set bits of `m` among the bits `0, …, n − 1`. -/
def pcUpTo (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pcUpTo m n + (bif m.testBit n then 1 else 0)

/-- One elimination step on coordinate `i`: the first word with bit `i` is dropped and added to the later words with
bit `i`. -/
def elimCol (i : Nat) : List Nat → List Nat
  | [] => []
  | p :: ps => if p.testBit i then ps.map (fun q => if q.testBit i then q ^^^ p else q) else p :: elimCol i ps

/-- Elimination steps on the coordinates `i < n` of `supp y`, from `n − 1` down to `0`. -/
def elim (y : Nat) : Nat → List Nat → List Nat
  | 0, ps => ps
  | n + 1, ps => elim y n (if y.testBit n then elimCol n ps else ps)

/-- The packed column of coordinate `i`: bit `k` is bit `i` of the `k`-th word. -/
def colOf (i : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (bif x.testBit i then 1 else 0) + 2 * colOf i xs

/-- The packed syndrome: bit `k` is the parity of `z ∧ x_k`, i.e. `⟨z, x_k⟩`. -/
def svOf (z : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (bif parityUpTo (z &&& x) 24 then 1 else 0) + 2 * svOf z xs

/-- `noE y s col n L acc`: no set `e` of at most `L` coordinates `i < n` outside `supp y` has
`acc + Σ_{i ∈ e} col i = s` (sums are exclusive or). -/
def noE (y s : Nat) (col : Nat → Nat) : Nat → Nat → Nat → Bool
  | 0, _, acc => acc != s
  | _ + 1, 0, acc => acc != s
  | n + 1, L + 1, acc => noE y s col n (L + 1) acc && (y.testBit n || noE y s col n L (acc ^^^ col n))

/-- The check of the word `y` (mask `a`, weight `w < T`) with `z` (mask `b`) on the words `xs`. -/
def leafCore (T a b w : Nat) (xs : List Nat) : Bool :=
  xs.all (fun x => x &&& a == 0) && noE a (svOf b xs) (fun i => colOf i xs) 24 ((T - w - 1) / 2) 0

/-- The leaf condition for the word `y` with mask `a` and `z` with mask `b`. -/
def leafOK (T a b : Nat) : Bool :=
  pcUpTo a 24 == 0 || (Nat.ble 6 (pcUpTo a 24) &&
    (Nat.ble T (pcUpTo a 24) || leafCore T a b (pcUpTo a 24) (elim a 24 yrows)))

/-- All words `y = a + Σ_{i<n} c_i y_{r+i}` (with `z = b + Σ_{i<n} c_i z_{r+i}`) pass `leafOK T`. -/
def go (T : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, a, b => leafOK T a b
  | n + 1, r, a, b => go T n (r + 1) a b && go T n (r + 1) (a ^^^ yrow r) (b ^^^ zrow r)

theorem go_12_00 : go 12 10 (0 + 1 + 1) 0 0 = true := by
  decide +kernel

theorem go_12_01 : go 12 10 (0 + 1 + 1) (0 ^^^ yrow (0 + 1)) (0 ^^^ zrow (0 + 1)) = true := by
  decide +kernel

theorem go_12_10 : go 12 10 (0 + 1 + 1) (0 ^^^ yrow 0) (0 ^^^ zrow 0) = true := by
  decide +kernel

theorem go_12_11 : go 12 10 (0 + 1 + 1) (0 ^^^ yrow 0 ^^^ yrow (0 + 1)) (0 ^^^ zrow 0 ^^^ zrow (0 + 1)) = true := by
  decide +kernel

/-- The whole check for `T = 12`: all `2¹²` words of `Y` pass. -/
theorem go_all : go 12 12 0 0 0 = true := by
  show (go 12 11 (0 + 1) 0 0 && go 12 11 (0 + 1) (0 ^^^ yrow 0) (0 ^^^ zrow 0)) = true
  show ((go 12 10 (0 + 1 + 1) 0 0 && go 12 10 (0 + 1 + 1) (0 ^^^ yrow (0 + 1)) (0 ^^^ zrow (0 + 1))) &&
    (go 12 10 (0 + 1 + 1) (0 ^^^ yrow 0) (0 ^^^ zrow 0) &&
      go 12 10 (0 + 1 + 1) (0 ^^^ yrow 0 ^^^ yrow (0 + 1)) (0 ^^^ zrow 0 ^^^ zrow (0 + 1)))) = true
  rw [go_12_00, go_12_01, go_12_10, go_12_11]
  rfl

end C72.T5.HD48
