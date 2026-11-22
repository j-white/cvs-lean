import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ThetaDecay
import Cvs.Zeta.ThetaTailSquared
import Cvs.Zeta.XiStrip

/-!
# The `t^{−1/2}` weight, and what is left of it

On the strip a zero occupies, both tail exponents are at most `−1/2`, not merely `≤ 0`.
Carrying that weight reduces the last item of the ceiling table to a single numeric
integral, `∫₁^∞ t^{−1/2}e^{−πt} dt`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Cvs.Zeta MeasureTheory

namespace Cvs.Zeta.ThetaWeightedTail
open Cvs.ZeroFree

/-- **On the zero strip the first exponent clears `−1/2`.** -/
theorem even_exponent_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : (s / 2 - 1).re ≤ -(1/2) := by
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [Complex.sub_re, hre]
  simp
  linarith

/-- **And so does the second.** -/
theorem cos_exponent_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1).re ≤ -(1/2) := by
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [Complex.sub_re, Complex.sub_re, hre]
  simp
  linarith

/-- **The tail with the weight kept.**  `J` bounds the weighted integral; the trivial
`J = e^{−π}/π` recovers `ZeroFreeHeightFive`'s statement. -/
theorem norm_kernel_tail_le_weighted {e : ℂ} (he : e.re ≤ -(1/2)) (C : ℝ) (hC : 0 ≤ C)
    (K : ℝ → ℝ)
    (hK : ∀ t : ℝ, 1 ≤ t → |K t - 1| ≤ C * Real.exp (-(Real.pi * t)))
    (J : ℝ)
    (hJint : IntegrableOn (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      (Set.Ioi (1:ℝ)))
    (hJ : (∫ t in Set.Ioi (1:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) ≤ J) :
    ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ e • (((K t : ℝ) : ℂ) - 1)‖ ≤ C * J := by
  have hint : IntegrableOn
      (fun t : ℝ => C * (t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))) (Set.Ioi (1:ℝ)) :=
    hJint.const_mul C
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    have htpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hpow : (t : ℝ) ^ e.re ≤ (t : ℝ) ^ (-(1/2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 he
    have hval : ‖((K t : ℝ) : ℂ) - 1‖ = |K t - 1| := by
      rw [show ((K t : ℝ) : ℂ) - 1 = ((K t - 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_real _
    rw [hval]
    have hpos : (0:ℝ) ≤ (t : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg htpos.le _
    calc (t : ℝ) ^ e.re * |K t - 1|
        ≤ (t : ℝ) ^ (-(1/2) : ℝ) * (C * Real.exp (-(Real.pi * t))) :=
          mul_le_mul hpow (hK t ht1) (abs_nonneg _) hpos
      _ = C * ((t : ℝ) ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) := by ring
  · rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hJ hC

/-- **`‖Λ₀‖` on the zero strip, over the weighted integral.**  Every input is `Cvs.Zeta.ThetaTailSquared`'s
except the integral, which is now the only quantity left to bound. -/
theorem norm_completedRiemannZeta₀_le_weighted {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (J : ℝ) (hJ0 : 0 ≤ J)
    (hJint : IntegrableOn (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      (Set.Ioi (1:ℝ)))
    (hJ : (∫ t in Set.Ioi (1:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) ≤ J) :
    ‖completedRiemannZeta₀ s‖ ≤ 2.0002 * J := by
  rw [completedRiemannZeta₀_eq_Lambda0, Lambda0_zeta_eq_tails, norm_div]
  have hA := norm_kernel_tail_le_weighted (even_exponent_le h0 h1) 2.0002 (by norm_num)
    (HurwitzZeta.evenKernel 0)
    (fun t ht => Cvs.Zeta.ThetaTailSquared.abs_evenKernel_sub_one_le_sq ht) J hJint hJ
  have hB := norm_kernel_tail_le_weighted (cos_exponent_le h0 h1) 2.0002 (by norm_num)
    (HurwitzZeta.cosKernel 0)
    (fun t ht => Cvs.Zeta.ThetaTailSquared.abs_cosKernel_sub_one_le_sq ht) J hJint hJ
  have hsum := le_trans (norm_add_le
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s / 2 - 1)
        • (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1)
        • (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1))) (add_le_add hA hB)
  rw [show ‖(2:ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **The height, over the weighted integral.**  With `J = e^{−π}/π` this is `Cvs.Zeta.ThetaTailSquared`'s
`5.94`; the true integral is `0.01223` against that `0.013755`, worth `6.33`. -/
theorem abs_im_gt_of_weighted {s : ℂ} (h : riemannXi s = 0) (J d : ℝ) (hJ0 : 0 ≤ J)
    (hJint : IntegrableOn (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      (Set.Ioi (1:ℝ)))
    (hJ : (∫ t in Set.Ioi (1:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) ≤ J)
    (hd0 : 0 ≤ d) (hkey : 2.0002 * J * (1 + d ^ 2) < 1) : d < |s.im| := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_mem_strip h
  have hL := norm_completedRiemannZeta₀_le_weighted h0.le h1.le J hJ0 hJint hJ
  have hns : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hns1 : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  have hA : ‖s‖ ^ 2 ≤ 1 + s.im ^ 2 := by rw [hns]; nlinarith
  have hB : ‖s - 1‖ ^ 2 ≤ 1 + s.im ^ 2 := by rw [hns1]; nlinarith
  have hprod : ‖s‖ * ‖s - 1‖ ≤ 1 + s.im ^ 2 := by
    have hsq : (‖s‖ * ‖s - 1‖) ^ 2 ≤ (1 + s.im ^ 2) ^ 2 := by
      have := mul_le_mul hA hB (by positivity) (by positivity)
      nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
    nlinarith [norm_nonneg s, norm_nonneg (s - 1), sq_nonneg s.im,
      mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1))]
  have hxi : riemannXi s - 1 / 2 = s * (s - 1) * completedRiemannZeta₀ s / 2 := by
    rw [riemannXi]; ring
  have hhalf : ‖riemannXi s - 1 / 2‖ = 1 / 2 := by
    rw [h, zero_sub, norm_neg, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
  have hbd : (1:ℝ) / 2 ≤ (1 + s.im ^ 2) * (2.0002 * J) / 2 := by
    rw [← hhalf, hxi, norm_div, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    have hstep : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ (1 + s.im ^ 2) * (2.0002 * J) :=
      mul_le_mul hprod hL (norm_nonneg _) (by positivity)
    linarith
  have h1' : (1:ℝ) ≤ (1 + s.im ^ 2) * (2.0002 * J) := by linarith
  have ht2 : d ^ 2 < s.im ^ 2 := by nlinarith
  nlinarith [sq_abs s.im, abs_nonneg s.im]

end Cvs.Zeta.ThetaWeightedTail
