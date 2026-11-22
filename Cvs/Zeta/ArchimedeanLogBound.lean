import Mathlib
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.GammaRLogDeriv

/-!
# The archimedean term is `O(log|t|)`
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.ZeroCounting

/-- `‖log π‖ ≤ 2`. -/
theorem norm_log_pi_le : ‖Complex.log ((Real.pi : ℝ) : ℂ)‖ ≤ 2 := by
  rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  have h1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h0 : 0 ≤ Real.log Real.pi := Real.log_nonneg h1
  rw [abs_of_nonneg h0]
  have hle : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4] at hle
  linarith [Real.log_two_lt_d9]

/-- **The archimedean log-derivative is `O(log|t|)` on the strip.** -/
theorem exists_norm_logDeriv_gammaR_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖logDeriv Gammaℝ s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_digamma_le_strip (1/4) 1
  refine ⟨2 + C₀, by linarith, fun s h1 h2 ht => ?_⟩
  have him : s.im ≠ 0 := by
    intro hc
    rw [hc] at ht
    simp at ht
    linarith
  have hhalf_im : (s / 2).im = s.im / 2 := by simp
  have hhalf_re : (s / 2).re = s.re / 2 := by simp
  have hne : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m
    refine ne_neg_nat_of_im_ne_zero ?_ m
    rw [hhalf_im]
    intro hc
    exact him (by linarith [hc])
  rw [logDeriv_gammaR hne]
  -- bound the digamma
  have hdim : (1:ℝ) ≤ |(s / 2).im| := by
    rw [hhalf_im, abs_div, abs_two]
    linarith
  have hdig := hC₀ (s / 2) (by rw [hhalf_re]; linarith) (by rw [hhalf_re]; linarith) hdim
  have hmono : Real.log (2 + |(s / 2).im|) ≤ Real.log (2 + |s.im|) := by
    refine Real.log_le_log (by positivity) ?_
    rw [hhalf_im, abs_div, abs_two]
    linarith [abs_nonneg s.im]
  have hlogpos : (0:ℝ) ≤ Real.log (2 + |s.im|) := by
    refine Real.log_nonneg ?_
    linarith [abs_nonneg s.im]
  have hdig' : ‖Complex.digamma (s / 2)‖ ≤ C₀ * (1 + Real.log (2 + |s.im|)) := by
    refine hdig.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hC₀0
  calc ‖-(Complex.log ((Real.pi : ℝ) : ℂ)) / 2 + Complex.digamma (s / 2) / 2‖
      ≤ ‖-(Complex.log ((Real.pi : ℝ) : ℂ)) / 2‖ + ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
    _ = ‖Complex.log ((Real.pi : ℝ) : ℂ)‖ / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        rw [norm_div, norm_div, norm_neg, show ‖(2:ℂ)‖ = 2 by norm_num]
    _ ≤ 2 / 2 + (C₀ * (1 + Real.log (2 + |s.im|))) / 2 := by
        linarith [norm_log_pi_le, hdig']
    _ ≤ (2 + C₀) * (1 + Real.log (2 + |s.im|)) := by nlinarith

end Cvs.ZeroCounting
