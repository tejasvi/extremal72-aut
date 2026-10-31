import C72T3.MDef
import C72T3.L23Check

/-!
# T3: Lemma 2.3 (no heavy isotropic vector), from the kernel check `C72T3.L23Check`

**Lemma 2.3.** No nonzero `v ∈ 𝔽₁₆⁷` with `⟨v, v⟩ = 0` satisfies `M(λv) ≥ 16` for all `λ ∈ 𝔽₁₆^×`.

The proof links the check `L23.chk 16` to `M`:
* the norm classes `c_i = cls (v_i)` satisfy `c₀ ⊕ … ⊕ c₆ = 0` when `⟨v, v⟩ = 0` (`xor_cls_eq_zero`), so the
  check covers the pattern of `v` (`okPat_all`);
* for the scaling `λ_r`, `|ψ(λ_r v_i)| = wr r c_i` (`wpsi_wr`);
* each word of the check is one of the 16 words of `e8` (`words_mem`), and its term is `sideTerm`
  (`sideTerm_word`), so `M(λ_r v) ≤ term` (`M_lam_le`).
-/

namespace C72.T3

open Finset

/-! ## Unfolding the check -/

theorem mem_cs : ∀ c, c < 4 → c ∈ L23.cs := by decide

theorem chk16 : ∀ c0, c0 < 4 → L23.chk 16 c0 = true := by
  intro c0 h
  interval_cases c0
  · exact L23.chk16_0
  · exact L23.chk16_1
  · exact L23.chk16_2
  · exact L23.chk16_3

/-- Every pattern with `c₆ = c₀ ⊕ … ⊕ c₅` passes the check. -/
theorem okPat_all (c0 c1 c2 c3 c4 c5 : ℕ) (h0 : c0 < 4) (h1 : c1 < 4) (h2 : c2 < 4) (h3 : c3 < 4)
    (h4 : c4 < 4) (h5 : c5 < 4) :
    L23.okPat 16 c0 c1 c2 c3 c4 c5 (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ c5) = true := by
  have hc := chk16 c0 h0
  simp only [L23.chk, List.all_eq_true] at hc
  exact hc c1 (mem_cs c1 h1) c2 (mem_cs c2 h2) c3 (mem_cs c3 h3) c4 (mem_cs c4 h4) c5 (mem_cs c5 h5)

theorem xor_last : ∀ x, x < 4 → ∀ y, y < 4 → x ^^^ y = 0 → y = x := by decide

/-! ## The words of the check and `M` -/

/-- The point set `S` of a word of the check. -/
def L23.Word.toFinset (q : L23.Word) : Finset (Fin 7) :=
  univ.filter fun i => q.bit i.val = true

/-- Each word of the check is one of the 16 words of `e8`. -/
theorem words_mem : ∀ q ∈ L23.words, (q.toFinset, q.x) ∈ e8Words := by decide +kernel

/-- The term of a word of the check is the bracket `sideTerm` of Sec. 2.3. -/
theorem sideTerm_word (q : L23.Word) (w : Fin 7 → ℕ) (hw : ∀ i, w i ≤ 5) :
    sideTerm w (q.toFinset, q.x) = L23.term q (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) := by
  rw [sideTerm_eq w hw]
  have h : ∀ i : Fin 7, (if i ∈ q.toFinset then 5 - w i else w i) = L23.tc (q.bit i.val) (w i) := by
    intro i
    simp only [L23.Word.toFinset, mem_filter, mem_univ, true_and, L23.tc, Bool.cond_eq_ite]
  rw [Finset.sum_congr rfl (fun i _ => h i), Fin.sum_univ_seven]
  simp only [L23.term, add_assoc]
  rfl

theorem wr_eq (r c : ℕ) : L23.wr r c = if c = 0 then 0 else if c = r then 4 else 2 := by
  unfold L23.wr
  by_cases h0 : c = 0 <;> by_cases h1 : c = r <;> simp [h0, h1]

/-- After the scaling `λ_r`, `|ψ(λ_r y)| = wr r (cls y)`. -/
theorem wpsi_wr (r : ℕ) (hr4 : r < 4) (hr1 : 1 ≤ r) (y : F16) : wpsi (lam r * y) = L23.wr r (cls y) := by
  rw [wpsi_lam r hr4 hr1 y, wr_eq]

theorem M_lam_le (r : ℕ) (hr4 : r < 4) (hr1 : 1 ≤ r) (v : Fin 7 → F16) {q : L23.Word}
    (hq : q ∈ L23.words) :
    M (lam r • v) ≤ L23.term q (L23.wr r (cls (v 0))) (L23.wr r (cls (v 1))) (L23.wr r (cls (v 2)))
      (L23.wr r (cls (v 3))) (L23.wr r (cls (v 4))) (L23.wr r (cls (v 5))) (L23.wr r (cls (v 6))) := by
  have h := M_le (lam r • v) (words_mem q hq)
  rw [sideTerm_word q _ (fun i => (wpsi_le _).trans (by norm_num))] at h
  simp only [Pi.smul_apply, smul_eq_mul, wpsi_wr r hr4 hr1] at h
  exact h

/-! ## Isotropy and the exclusive or of the classes -/

theorem xor_cls_eq_zero (v : Fin 7 → F16) (hiso : herm v v = 0) :
    cls (v 0) ^^^ cls (v 1) ^^^ cls (v 2) ^^^ cls (v 3) ^^^ cls (v 4) ^^^ cls (v 5) ^^^ cls (v 6) = 0 := by
  have hc : ∀ i, cls (v i) < 4 := fun i => cls_lt _
  have x1 := xor_lt_four _ (hc 0) _ (hc 1)
  have x2 := xor_lt_four _ x1 _ (hc 2)
  have x3 := xor_lt_four _ x2 _ (hc 3)
  have x4 := xor_lt_four _ x3 _ (hc 4)
  have x5 := xor_lt_four _ x4 _ (hc 5)
  have x6 := xor_lt_four _ x5 _ (hc 6)
  have e : herm v v = Nc (cls (v 0) ^^^ cls (v 1) ^^^ cls (v 2) ^^^ cls (v 3) ^^^ cls (v 4) ^^^ cls (v 5) ^^^
      cls (v 6)) := by
    rw [herm, Fin.sum_univ_seven]
    simp only [norm_cls]
    rw [← Nc_xor _ (hc 0) _ (hc 1), ← Nc_xor _ x1 _ (hc 2), ← Nc_xor _ x2 _ (hc 3), ← Nc_xor _ x3 _ (hc 4),
      ← Nc_xor _ x4 _ (hc 5), ← Nc_xor _ x5 _ (hc 6)]
  rw [e] at hiso
  exact (Nc_eq_zero _ x6).1 hiso

/-! ## Lemma 2.3 -/

/-- **Lemma 2.3.** No nonzero `v ∈ 𝔽₁₆⁷` with `⟨v, v⟩ = 0` satisfies `M(λv) ≥ 16` for all `λ ∈ 𝔽₁₆^×`. -/
theorem lemma23 (v : Fin 7 → F16) (hv : v ≠ 0) (hiso : herm v v = 0) : ∃ l : F16, l ≠ 0 ∧ M (l • v) < 16 := by
  have hc : ∀ i, cls (v i) < 4 := fun i => cls_lt _
  have x5 : cls (v 0) ^^^ cls (v 1) ^^^ cls (v 2) ^^^ cls (v 3) ^^^ cls (v 4) ^^^ cls (v 5) < 4 :=
    xor_lt_four _ (xor_lt_four _ (xor_lt_four _ (xor_lt_four _ (xor_lt_four _ (hc 0) _ (hc 1)) _ (hc 2)) _
      (hc 3)) _ (hc 4)) _ (hc 5)
  have h6 := xor_last _ x5 _ (hc 6) (xor_cls_eq_zero v hiso)
  have hok := okPat_all _ _ _ _ _ _ (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
  rw [← h6] at hok
  simp only [L23.okPat, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hok
  rcases hok with hzero | ⟨q, hq, hsmall⟩
  · exfalso
    apply hv
    obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6'⟩ := hzero
    funext i
    fin_cases i
    · exact (cls_eq_zero _).1 h0
    · exact (cls_eq_zero _).1 h1
    · exact (cls_eq_zero _).1 h2
    · exact (cls_eq_zero _).1 h3
    · exact (cls_eq_zero _).1 h4
    · exact (cls_eq_zero _).1 h5
    · exact (cls_eq_zero _).1 h6'
  · simp only [L23.smallFor, Bool.or_eq_true, Nat.blt_eq] at hsmall
    rcases hsmall with (h | h) | h
    · exact ⟨lam 1, lam_ne_zero 1 (by norm_num), lt_of_le_of_lt (M_lam_le 1 (by norm_num) le_rfl v hq) h⟩
    · exact ⟨lam 2, lam_ne_zero 2 (by norm_num),
        lt_of_le_of_lt (M_lam_le 2 (by norm_num) (by norm_num) v hq) h⟩
    · exact ⟨lam 3, lam_ne_zero 3 (by norm_num),
        lt_of_le_of_lt (M_lam_le 3 (by norm_num) (by norm_num) v hq) h⟩

end C72.T3
