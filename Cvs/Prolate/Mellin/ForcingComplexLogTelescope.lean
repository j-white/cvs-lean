import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen forcing telescopes in complex logarithms

If `exp x = exp y` and `|Im x − Im y| < 2π` then `x = y`. Hence, with principal logarithms and `p, q` in the right
half-plane: from `(1 − β)(1 + A) = p` and `(1 + A)² = pq − e`, `|β − ½(log q − log p)| ≤ |β|² + ¾|e/(pq)|`; from
`q(1 + r′) − p′(1 + r) = D` with `q/p′` and `(1 + r′)/(1 + r)` within `½` of `1`,
`|log q − log p′ − log(1 + r) + log(1 + r′)| ≤ (3/2)|D/(p′(1 + r))|`; and the two telescope along a line.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.ForcingComplexLogTelescope

/-- Two logarithms of the same number whose imaginary parts differ by less than `2π` agree. -/
theorem eq_of_exp_eq {x y : ℂ} (h : exp x = exp y) (hi : |x.im - y.im| < 2 * Real.pi) : x = y := by
  have h1 : exp (x - y) = 1 := by rw [exp_sub, h, div_self (exp_ne_zero y)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have him : (x - y).im = n * (2 * Real.pi) := by rw [hn]; simp
  rw [sub_im] at him
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hi
  have : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hn0 : n = 0 := by
    have := abs_lt.mp this
    have h1 : (-1 : ℝ) < n := this.1
    have h2 : (n : ℝ) < 1 := this.2
    have : -1 < n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  rw [hn0] at hn
  simpa [sub_eq_zero] using hn

/-- `|log(1 + z)| ≤ (3/2)|z|` for `|z| ≤ ½`. -/
theorem norm_log_one_add_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖Complex.log (1 + z)‖ ≤ 3 / 2 * ‖z‖ := by
  have h := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
  have h1 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 := by
    have : (1 - ‖z‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hz0 := norm_nonneg z
    calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖z‖ * ‖z‖ := by ring
      _ ≤ ‖z‖ * (1 / 2) := by gcongr
      _ = ‖z‖ / 2 := by ring
  have := norm_add_le (Complex.log (1 + z) - z) z
  rw [sub_add_cancel] at this
  linarith

/-- `|log(1 − β) + β| ≤ |β|²` for `|β| ≤ ½`. -/
theorem norm_log_one_sub_add_le {β : ℂ} (hβ : ‖β‖ ≤ 1 / 2) : ‖Complex.log (1 - β) + β‖ ≤ ‖β‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -β) (by rw [norm_neg]; linarith)
  rw [norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h
  refine h.trans ?_
  have : (1 - ‖β‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have := sq_nonneg ‖β‖
  calc ‖β‖ ^ 2 * (1 - ‖β‖)⁻¹ / 2 ≤ ‖β‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖β‖ ^ 2 := by ring

theorem abs_im_log_lt_of_re_pos {z : ℂ} (hz : 0 < z.re) : |(Complex.log z).im| < Real.pi / 2 := by
  rw [Complex.log_im, abs_lt]
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  exact abs_lt.mp h

theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by rw [h] at hz; simp at hz

/-- **The complex step.** -/
theorem step_c {β A p q e : ℂ} (h1 : (1 - β) * (1 + A) = p) (h2 : (1 + A) ^ 2 = p * q - e) (hA : 1 + A ≠ 0)
    (hp : 0 < p.re) (hq : 0 < q.re) (hβ : ‖β‖ ≤ 1 / 2) (hw : ‖e / (p * q)‖ ≤ 1 / 2) :
    ‖β - 1 / 2 * (Complex.log q - Complex.log p)‖ ≤ ‖β‖ ^ 2 + 3 / 4 * ‖e / (p * q)‖ := by
  have hp0 := ne_zero_of_re_pos hp
  have hq0 := ne_zero_of_re_pos hq
  have hβ1 : 1 - β ≠ 0 := by
    intro h0; have : ‖β‖ = 1 := by rw [show β = 1 by linear_combination -h0]; simp
    linarith
  set u := e / (p * q)
  have hu1 : 1 - u ≠ 0 := by
    intro h0; have : ‖u‖ = 1 := by rw [show u = 1 by linear_combination -h0]; simp
    linarith
  set L := Complex.log (1 - β)
  set M := Complex.log (1 - u)
  -- `2L = log p − log q − M`
  have hexp : exp (2 * L) = exp (Complex.log p - Complex.log q - M) := by
    rw [show 2 * L = L + L by ring, exp_add, exp_sub, exp_sub, exp_log hβ1, exp_log hp0, exp_log hq0,
      exp_log hu1]
    have hpq : p * q - e ≠ 0 := by rw [← h2]; exact pow_ne_zero 2 hA
    have e1 : 1 - u = (p * q - e) / (p * q) := by simp only [u]; field_simp
    rw [e1, ← h2, ← h1]
    field_simp
  have hL : ‖L‖ ≤ 3 / 4 := by
    have := norm_log_one_add_le (z := -β) (by rw [norm_neg]; exact hβ)
    rw [← sub_eq_add_neg, norm_neg] at this; linarith
  have hM : ‖M‖ ≤ 3 / 4 := by
    have := norm_log_one_add_le (z := -u) (by rw [norm_neg]; exact hw)
    rw [← sub_eq_add_neg, norm_neg] at this; linarith
  have hip := abs_im_log_lt_of_re_pos hp
  have hiq := abs_im_log_lt_of_re_pos hq
  have hi : |(2 * L).im - (Complex.log p - Complex.log q - M).im| < 2 * Real.pi := by
    have a1 : |(2 * L).im| ≤ 3 / 2 := by
      have : |(2 * L).im| ≤ ‖2 * L‖ := Complex.abs_im_le_norm _
      rw [norm_mul, Complex.norm_ofNat] at this; linarith
    have a2 : |M.im| ≤ 3 / 4 := (Complex.abs_im_le_norm M).trans hM
    simp only [sub_im]
    have hpi := Real.pi_gt_three
    calc |(2 * L).im - ((Complex.log p).im - (Complex.log q).im - M.im)|
        ≤ |(2 * L).im| + |(Complex.log p).im| + |(Complex.log q).im| + |M.im| := by
          have := abs_sub (2 * L).im ((Complex.log p).im - (Complex.log q).im - M.im)
          have := abs_sub ((Complex.log p).im - (Complex.log q).im) M.im
          have := abs_sub (Complex.log p).im (Complex.log q).im
          linarith
      _ < 2 * Real.pi := by linarith
  have hkey := eq_of_exp_eq hexp hi
  have e2 : β - 1 / 2 * (Complex.log q - Complex.log p) = (L + β) + 1 / 2 * M := by
    linear_combination (-1 / 2 : ℂ) * hkey
  rw [e2]
  have hb := norm_log_one_sub_add_le hβ
  have hm := norm_log_one_add_le (z := -u) (by rw [norm_neg]; exact hw)
  rw [← sub_eq_add_neg, norm_neg] at hm
  calc ‖L + β + 1 / 2 * M‖ ≤ ‖L + β‖ + ‖1 / 2 * M‖ := norm_add_le _ _
    _ ≤ ‖β‖ ^ 2 + 1 / 2 * (3 / 2 * ‖u‖) := by
        rw [norm_mul]; norm_num; gcongr
    _ = ‖β‖ ^ 2 + 3 / 4 * ‖u‖ := by ring

/-- `log z − log w = log(z/w)` for `z, w` in the right half-plane with `|z/w − 1| ≤ ½`. -/
theorem log_sub_log_eq {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) (hs : ‖z / w - 1‖ ≤ 1 / 2) :
    Complex.log z - Complex.log w = Complex.log (1 + (z / w - 1)) := by
  have hz0 := ne_zero_of_re_pos hz
  have hw0 := ne_zero_of_re_pos hw
  have hne : 1 + (z / w - 1) ≠ 0 := by rw [add_sub_cancel]; exact div_ne_zero hz0 hw0
  apply eq_of_exp_eq
  · rw [exp_sub, exp_log hz0, exp_log hw0, exp_log hne, add_sub_cancel]
  · have h1 := abs_im_log_lt_of_re_pos hz
    have h2 := abs_im_log_lt_of_re_pos hw
    have h3 : |(Complex.log (1 + (z / w - 1))).im| ≤ 3 / 4 :=
      (Complex.abs_im_le_norm _).trans (by have := norm_log_one_add_le hs; linarith)
    rw [sub_im]
    have hpi := Real.pi_gt_three
    calc |(Complex.log z).im - (Complex.log w).im - (Complex.log (1 + (z / w - 1))).im|
        ≤ |(Complex.log z).im| + |(Complex.log w).im| + |(Complex.log (1 + (z / w - 1))).im| := by
          have := abs_sub ((Complex.log z).im - (Complex.log w).im) (Complex.log (1 + (z / w - 1))).im
          have := abs_sub (Complex.log z).im (Complex.log w).im
          linarith
      _ < 2 * Real.pi := by linarith

/-- **The complex shift.** -/
theorem shift_c {q p' r r' D : ℂ} (h : q * (1 + r') - p' * (1 + r) = D) (hq : 0 < q.re) (hp' : 0 < p'.re)
    (hr : 0 < (1 + r).re) (hr' : 0 < (1 + r').re) (hs1 : ‖q / p' - 1‖ ≤ 1 / 2)
    (hs2 : ‖(1 + r') / (1 + r) - 1‖ ≤ 1 / 2) (hD : ‖D / (p' * (1 + r))‖ ≤ 1 / 2) :
    ‖Complex.log q - Complex.log p' - Complex.log (1 + r) + Complex.log (1 + r')‖
      ≤ 3 / 2 * ‖D / (p' * (1 + r))‖ := by
  have hq0 := ne_zero_of_re_pos hq
  have hp0 := ne_zero_of_re_pos hp'
  have hr0 := ne_zero_of_re_pos hr
  have hr0' := ne_zero_of_re_pos hr'
  have e1 := log_sub_log_eq hq hp' hs1
  have e2 := log_sub_log_eq hr' hr hs2
  set X := Complex.log (1 + (q / p' - 1)) + Complex.log (1 + ((1 + r') / (1 + r) - 1))
  have hX : Complex.log q - Complex.log p' - Complex.log (1 + r) + Complex.log (1 + r') = X := by
    simp only [X]; rw [← e1, ← e2]; ring
  rw [hX]
  set u := D / (p' * (1 + r))
  have hu1 : 1 + u ≠ 0 := by
    intro h0; have : ‖u‖ = 1 := by rw [show u = -1 by linear_combination h0]; simp
    linarith
  have hXeq : X = Complex.log (1 + u) := by
    apply eq_of_exp_eq
    · simp only [X]
      rw [exp_add, exp_log (by rw [add_sub_cancel]; exact div_ne_zero hq0 hp0),
        exp_log (by rw [add_sub_cancel]; exact div_ne_zero hr0' hr0), exp_log hu1]
      simp only [u, add_sub_cancel]
      rw [← h]; field_simp; ring
    · have a1 : ‖Complex.log (1 + (q / p' - 1))‖ ≤ 3 / 4 := by have := norm_log_one_add_le hs1; linarith
      have a2 : ‖Complex.log (1 + ((1 + r') / (1 + r) - 1))‖ ≤ 3 / 4 := by
        have := norm_log_one_add_le hs2; linarith
      have a3 : ‖Complex.log (1 + u)‖ ≤ 3 / 4 := by have := norm_log_one_add_le hD; linarith
      have b1 := (Complex.abs_im_le_norm (Complex.log (1 + (q / p' - 1)))).trans a1
      have b2 := (Complex.abs_im_le_norm (Complex.log (1 + ((1 + r') / (1 + r) - 1)))).trans a2
      have b3 := (Complex.abs_im_le_norm (Complex.log (1 + u))).trans a3
      simp only [X, add_im]
      have hpi := Real.pi_gt_three
      calc |(Complex.log (1 + (q / p' - 1))).im + (Complex.log (1 + ((1 + r') / (1 + r) - 1))).im
            - (Complex.log (1 + u)).im|
          ≤ |(Complex.log (1 + (q / p' - 1))).im| + |(Complex.log (1 + ((1 + r') / (1 + r) - 1))).im|
            + |(Complex.log (1 + u)).im| := by
            have := abs_sub ((Complex.log (1 + (q / p' - 1))).im
              + (Complex.log (1 + ((1 + r') / (1 + r) - 1))).im) (Complex.log (1 + u)).im
            have := abs_add_le (Complex.log (1 + (q / p' - 1))).im
              (Complex.log (1 + ((1 + r') / (1 + r) - 1))).im
            linarith
        _ < 2 * Real.pi := by linarith
  rw [hXeq]
  exact norm_log_one_add_le hD

/-- **The telescope.** -/
theorem sum_c_le {β ℓp ℓq ℓr : ℕ → ℂ} {e1 e2 : ℕ → ℝ} (K : ℕ)
    (hstep : ∀ k < K, ‖β k - 1 / 2 * (ℓq k - ℓp k)‖ ≤ e1 k)
    (hshift : ∀ k < K, ‖ℓq k - ℓp (k + 1) - ℓr k + ℓr (k + 1)‖ ≤ e2 k) :
    ‖∑ k ∈ range K, β k - 1 / 2 * (ℓp K - ℓp 0) + 1 / 2 * (ℓr K - ℓr 0)‖
      ≤ ∑ k ∈ range K, (e1 k + 1 / 2 * e2 k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, sum_range_succ]
    have ih' := ih (fun k hk => hstep k (by omega)) (fun k hk => hshift k (by omega))
    have a := hstep K (by omega)
    have b := hshift K (by omega)
    have e : ∑ k ∈ range K, β k + β K - 1 / 2 * (ℓp (K + 1) - ℓp 0) + 1 / 2 * (ℓr (K + 1) - ℓr 0)
        = (∑ k ∈ range K, β k - 1 / 2 * (ℓp K - ℓp 0) + 1 / 2 * (ℓr K - ℓr 0))
          + (β K - 1 / 2 * (ℓq K - ℓp K)) + 1 / 2 * (ℓq K - ℓp (K + 1) - ℓr K + ℓr (K + 1)) := by ring
    rw [e]
    calc _ ≤ ‖∑ k ∈ range K, β k - 1 / 2 * (ℓp K - ℓp 0) + 1 / 2 * (ℓr K - ℓr 0)‖
          + ‖β K - 1 / 2 * (ℓq K - ℓp K)‖ + ‖1 / 2 * (ℓq K - ℓp (K + 1) - ℓr K + ℓr (K + 1))‖ := by
          refine (norm_add_le _ _).trans ?_; gcongr; exact norm_add_le _ _
      _ ≤ _ := by
          rw [norm_mul]; norm_num
          linarith

end Cvs.Prolate.Mellin.ForcingComplexLogTelescope
