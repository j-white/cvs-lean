import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The modulus of Gamma off the real axis

For real `x ≥ 1` and `y`: `exp(−y²/x)‖Γ(x)‖ ≤ ‖Γ(x + iy)‖ ≤ ‖Γ(x)‖`, by Euler's limit formula factor by factor.
-/

noncomputable section

open Complex Filter Topology Finset

namespace Cvs.Upstream.GammaModulusOffAxis

/-- One factor: `exp(−y²/(2t²)) t ≤ ‖t + iy‖` and `t ≤ ‖t + iy‖` for `t > 0`. -/
theorem factor_bounds {t y : ℝ} (ht : 0 < t) :
    t ≤ ‖(t : ℂ) + I * y‖ ∧ Real.exp (-(y ^ 2 / (2 * t ^ 2))) * ‖(t : ℂ) + I * y‖ ≤ t := by
  have hn : ‖(t : ℂ) + I * y‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  rw [hn]
  constructor
  · rw [Real.le_sqrt ht.le (by positivity)]; nlinarith [sq_nonneg y]
  · -- `√(t² + y²) ≤ t exp(y²/(2t²))`
    have h1 : Real.sqrt (t ^ 2 + y ^ 2) ≤ t * Real.exp (y ^ 2 / (2 * t ^ 2)) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hx : 1 + y ^ 2 / t ^ 2 ≤ Real.exp (y ^ 2 / t ^ 2) := by
        have := Real.add_one_le_exp (y ^ 2 / t ^ 2); linarith
      have he : Real.exp (y ^ 2 / (2 * t ^ 2)) ^ 2 = Real.exp (y ^ 2 / t ^ 2) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
      rw [mul_pow, he]
      have : t ^ 2 + y ^ 2 = t ^ 2 * (1 + y ^ 2 / t ^ 2) := by field_simp
      rw [this]; gcongr
    have h2 : Real.exp (-(y ^ 2 / (2 * t ^ 2))) * Real.exp (y ^ 2 / (2 * t ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(y ^ 2 / (2 * t ^ 2))) * Real.sqrt (t ^ 2 + y ^ 2)
        ≤ Real.exp (-(y ^ 2 / (2 * t ^ 2))) * (t * Real.exp (y ^ 2 / (2 * t ^ 2))) := by gcongr
      _ = t := by rw [mul_comm t, ← mul_assoc, h2, one_mul]

/-- `Σ_{j ≤ n} 1/(x+j)² ≤ 2/x` for `x ≥ 1`. -/
theorem sum_inv_sq_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : ∑ j ∈ range (n + 1), 1 / (x + j) ^ 2 ≤ 2 / x := by
  have key : ∀ n : ℕ, ∑ j ∈ range (n + 1), 1 / (x + j) ^ 2 ≤ 1 / x ^ 2 + (1 / x - 1 / (x + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : 0 < x + (n : ℝ) := by have := n.cast_nonneg (α := ℝ); linarith
      have : 1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (x + n) - 1 / (x + ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        rw [show 1 / (x + n) - 1 / (x + (n + 1)) = 1 / ((x + n) * (x + n + 1)) by field_simp; ring]
        apply one_div_le_one_div_of_le (by positivity); nlinarith
      linarith
  refine (key n).trans ?_
  have : 0 ≤ 1 / (x + n) := by have := n.cast_nonneg (α := ℝ); positivity
  have : 1 / x ^ 2 ≤ 1 / x := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  have : 2 / x = 1 / x + 1 / x := by ring
  linarith

/-- **Euler's limit factor by factor.** -/
theorem norm_GammaSeq_bounds {x y : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq ((x : ℂ) + I * y) n‖ ≤ ‖GammaSeq (x : ℂ) n‖
      ∧ Real.exp (-(y ^ 2 / x)) * ‖GammaSeq (x : ℂ) n‖ ≤ ‖GammaSeq ((x : ℂ) + I * y) n‖ := by
  have hx0 : 0 < x := by linarith
  unfold GammaSeq
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_natCast_cpow_of_pos hn, norm_natCast_cpow_of_pos hn,
    Complex.norm_prod, Complex.norm_prod]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  have hpos : ∀ j ∈ range (n + 1), 0 < x + (j : ℝ) := fun j _ => by have := j.cast_nonneg (α := ℝ); linarith
  have e1 : ∀ j ∈ range (n + 1), ‖(x : ℂ) + (j : ℂ)‖ = x + j := fun j hj => by
    rw [show (x : ℂ) + (j : ℂ) = ((x + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (hpos j hj).le]
  have e2 : ∀ j ∈ range (n + 1), ‖(x : ℂ) + I * y + (j : ℂ)‖ = ‖((x + j : ℝ) : ℂ) + I * y‖ := fun j _ => by
    push_cast; ring_nf
  rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2]
  set A := (n : ℝ) ^ x * ‖((Nat.factorial n : ℕ) : ℂ)‖
  have hA : 0 < A := by
    have : 0 < ‖((Nat.factorial n : ℕ) : ℂ)‖ := by rw [Complex.norm_natCast]; exact_mod_cast Nat.factorial_pos n
    positivity
  have hP1 : 0 < ∏ j ∈ range (n + 1), (x + (j : ℝ)) := Finset.prod_pos hpos
  have hle : ∏ j ∈ range (n + 1), (x + (j : ℝ)) ≤ ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖ :=
    Finset.prod_le_prod₀ (fun j hj => (hpos j hj).le) fun j hj => (factor_bounds (y := y) (hpos j hj)).1
  have hP2 : 0 < ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖ := lt_of_lt_of_le hP1 hle
  constructor
  · exact div_le_div_of_nonneg_left hA.le hP1 hle
  · -- `exp(−y²/x) Π ‖x + j + iy‖ ≤ Π (x + j)`
    have hprod : Real.exp (-(∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2)))
        * ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖ ≤ ∏ j ∈ range (n + 1), (x + (j : ℝ)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun j _ => by positivity) fun j hj => (factor_bounds (y := y) (hpos j hj)).2
    have hsum : ∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2) ≤ y ^ 2 / x := by
      have := sum_inv_sq_le hx n
      calc ∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2) = y ^ 2 / 2 * ∑ j ∈ range (n + 1), 1 / (x + j) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by field_simp
        _ ≤ y ^ 2 / 2 * (2 / x) := by gcongr
        _ = y ^ 2 / x := by field_simp
    have hexp : Real.exp (-(y ^ 2 / x)) ≤ Real.exp (-(∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2))) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [mul_div_assoc', div_le_div_iff₀ hP1 hP2]
    calc Real.exp (-(y ^ 2 / x)) * A * ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖
        ≤ Real.exp (-(∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2))) * A
            * ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖ := by gcongr
      _ = A * (Real.exp (-(∑ j ∈ range (n + 1), y ^ 2 / (2 * (x + j) ^ 2)))
            * ∏ j ∈ range (n + 1), ‖((x + j : ℝ) : ℂ) + I * y‖) := by ring
      _ ≤ A * ∏ j ∈ range (n + 1), (x + (j : ℝ)) := by gcongr

/-- **The modulus of Gamma off the real axis.** -/
theorem norm_Gamma_bounds {x y : ℝ} (hx : 1 ≤ x) :
    ‖Gamma ((x : ℂ) + I * y)‖ ≤ ‖Gamma (x : ℂ)‖ ∧ Real.exp (-(y ^ 2 / x)) * ‖Gamma (x : ℂ)‖ ≤ ‖Gamma ((x : ℂ) + I * y)‖ := by
  have t1 := (GammaSeq_tendsto_Gamma ((x : ℂ) + I * y)).norm
  have t2 := (GammaSeq_tendsto_Gamma (x : ℂ)).norm
  have ev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  constructor
  · exact le_of_tendsto_of_tendsto t1 t2 (ev.mono fun n hn => (norm_GammaSeq_bounds hx hn).1)
  · exact le_of_tendsto_of_tendsto (t2.const_mul _) t1 (ev.mono fun n hn => (norm_GammaSeq_bounds hx hn).2)

/-- `|log‖Γ(x+iy)‖ − log‖Γ(x)‖| ≤ y²/x` for `x ≥ 1`. -/
theorem abs_log_norm_Gamma_sub_le {x y : ℝ} (hx : 1 ≤ x) :
    |Real.log ‖Gamma ((x : ℂ) + I * y)‖ - Real.log ‖Gamma (x : ℂ)‖| ≤ y ^ 2 / x := by
  obtain ⟨h1, h2⟩ := norm_Gamma_bounds (y := y) hx
  have hG : 0 < ‖Gamma (x : ℂ)‖ := by
    rw [Complex.Gamma_ofReal]; rw [Complex.norm_real]
    exact abs_pos.mpr (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2 : 0 < ‖Gamma ((x : ℂ) + I * y)‖ := lt_of_lt_of_le (by positivity) h2
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (Real.exp_pos _).ne' hG.ne', Real.log_exp] at this
    linarith
  · have := Real.log_le_log hG2 h1
    have : 0 ≤ y ^ 2 / x := by positivity
    linarith

end Cvs.Upstream.GammaModulusOffAxis
