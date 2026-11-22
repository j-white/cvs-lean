import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ThetaDecay
import Cvs.Zeta.XiStrip
import Cvs.Zeta.ZetaRealSegment

/-!
# Tightening the zero-free height to `|Im ρ| > 5`
-/

noncomputable section

open Complex Set MeasureTheory Cvs.Zeta

namespace Cvs.ZeroFree

/-- `e^π > 21`, from `e³ > 19.68` and `e^{π−3} ≥ 1 + (π−3) > 1.14`. -/
theorem exp_pi_gt_21 : (21 : ℝ) < Real.exp Real.pi := by
  have h314 : (3.14:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hx : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hfac : Real.exp 1 ^ 3 - 19.683
      = (Real.exp 1 - 2.7) * (Real.exp 1 ^ 2 + 2.7 * Real.exp 1 + 7.29) := by ring
  have hp1 : 0 < Real.exp 1 - 2.7 := by linarith
  have hp2 : 0 < Real.exp 1 ^ 2 + 2.7 * Real.exp 1 + 7.29 := by positivity
  have he3 : (19.683:ℝ) < Real.exp 3 := by
    rw [h1]; nlinarith [mul_pos hp1 hp2, hfac]
  -- `e^{π-3} ≥ 1 + (π-3)`
  have hlin : 1 + (Real.pi - 3) ≤ Real.exp (Real.pi - 3) := Real.add_one_le_exp _ |>.trans_eq' (by ring)
  have hsplit : Real.exp Real.pi = Real.exp 3 * Real.exp (Real.pi - 3) := by
    rw [← Real.exp_add]; congr 1; ring
  have hgt : (1.14:ℝ) < 1 + (Real.pi - 3) := by linarith
  have hepos : (0:ℝ) < Real.exp 3 := Real.exp_pos _
  rw [hsplit]
  nlinarith [he3, hlin, hgt, hepos]

/-- `∫₁^∞ e^{−πt} dt = e^{−π}/π`, with the `π` kept. -/
theorem integral_exp_neg_pi_Ioi_one :
    (∫ t in Set.Ioi (1:ℝ), Real.exp (-(Real.pi * t))) = Real.exp (-Real.pi) / Real.pi := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 1 hpi
  simp only [smul_eq_mul] at h
  rw [h, integral_exp_neg_Ioi, mul_one]
  ring

/-- The sharpened kernel bound: prefactor `2.1` instead of `4`. -/
theorem abs_evenKernel_sub_one_le_sharp {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.evenKernel 0 t - 1| ≤ 2.1 * Real.exp (-(Real.pi * t)) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have him : (0 : ℝ) < (I * (t : ℂ)).im := by simpa using htpos
  have hb := norm_jacobiTheta_sub_one_le him
  have him' : (I * (t : ℂ)).im = t := by simp
  rw [him'] at hb
  have hnorm : ‖jacobiTheta (I * (t : ℂ)) - 1‖ = |HurwitzZeta.evenKernel 0 t - 1| := by
    rw [← evenKernel_zero_eq_jacobiTheta t]
    rw [show ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1
        = ((HurwitzZeta.evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_real _
  rw [hnorm] at hb
  refine hb.trans ?_
  rw [← neg_mul]
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have h21 := exp_pi_gt_21
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hsmall : Real.exp (-Real.pi * t) ≤ Real.exp (-Real.pi) := by
    refine Real.exp_le_exp.mpr ?_; nlinarith
  have hinv : Real.exp (-Real.pi) < 1 / 21 := by
    rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]
    linarith
  have hpos : (0 : ℝ) < 1 - Real.exp (-Real.pi * t) := by linarith
  have hpre : 2 / (1 - Real.exp (-Real.pi * t)) ≤ 2.1 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  exact mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le

theorem abs_cosKernel_sub_one_le_sharp {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.cosKernel 0 t - 1| ≤ 2.1 * Real.exp (-(Real.pi * t)) := by
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  exact abs_evenKernel_sub_one_le_sharp ht

/-- The tail bound with the `π` kept. -/
theorem norm_kernel_tail_le_pi {e : ℂ} (he : e.re ≤ 0) (C : ℝ) (_hC : 0 ≤ C) (K : ℝ → ℝ)
    (hK : ∀ t : ℝ, 1 ≤ t → |K t - 1| ≤ C * Real.exp (-(Real.pi * t))) :
    ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ e • (((K t : ℝ) : ℂ) - 1)‖
      ≤ C * (Real.exp (-Real.pi) / Real.pi) := by
  have hint : IntegrableOn (fun t : ℝ => C * Real.exp (-(Real.pi * t))) (Set.Ioi (1:ℝ)) := by
    have h := exp_neg_integrableOn_Ioi (1:ℝ) (b := Real.pi) Real.pi_pos
    simp only [neg_mul] at h
    exact h.const_mul C
  refine (norm_integral_le_of_norm_le hint ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    have htpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hpow : (t : ℝ) ^ e.re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 he
    have hval : ‖((K t : ℝ) : ℂ) - 1‖ = |K t - 1| := by
      rw [show ((K t : ℝ) : ℂ) - 1 = ((K t - 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_real _
    rw [hval]
    calc (t : ℝ) ^ e.re * |K t - 1| ≤ 1 * (C * Real.exp (-(Real.pi * t))) :=
          mul_le_mul hpow (hK t ht1) (abs_nonneg _) zero_le_one
      _ = C * Real.exp (-(Real.pi * t)) := by ring
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_pi_Ioi_one]

/-- **`‖Λ₀‖ ≤ 2.1·e^{−π}/π ≈ 0.0289` on `−1 ≤ Re s ≤ 2`** — six times sharper than. -/
theorem norm_completedRiemannZeta₀_le_sharp {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 2.1 * (Real.exp (-Real.pi) / Real.pi) := by
  rw [completedRiemannZeta₀_eq_Lambda0, Lambda0_zeta_eq_tails, norm_div]
  have hre : (s / 2).re = s.re / 2 := by simp
  have he1 : (s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, hre]; simp; linarith
  have he2 : ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, Complex.sub_re, hre]; simp; linarith
  have hA := norm_kernel_tail_le_pi he1 2.1 (by norm_num) (HurwitzZeta.evenKernel 0)
    (fun t ht => abs_evenKernel_sub_one_le_sharp ht)
  have hB := norm_kernel_tail_le_pi he2 2.1 (by norm_num) (HurwitzZeta.cosKernel 0)
    (fun t ht => abs_cosKernel_sub_one_le_sharp ht)
  have hsum := le_trans (norm_add_le
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s / 2 - 1)
        • (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1)
        • (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1))) (add_le_add hA hB)
  rw [show ‖(2:ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- The tightened constant is below `1/26`. -/
theorem const_lt : 2.1 * (Real.exp (-Real.pi) / Real.pi) < 1 / 26 := by
  have h21 := exp_pi_gt_21
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hE : (0:ℝ) < Real.exp (-Real.pi) := Real.exp_pos _
  have hinv : Real.exp (-Real.pi) < 1 / 21 := by
    rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]
    linarith
  have h314 : (3.14:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hkey : 54.6 * Real.exp (-Real.pi) < Real.pi := by nlinarith
  rw [mul_div_assoc', div_lt_iff₀ hpipos]
  linarith

/-- **The tightened zero-free height.**  Every zero of `ξ` has `|Im ρ| > 5`. -/
theorem abs_im_gt_five_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) : 5 < |s.im| := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_mem_strip h
  have hL := norm_completedRiemannZeta₀_le_sharp (s := s) (by linarith) (by linarith)
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
  have hbd : (1:ℝ) / 2
      ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) / 2 := by
    rw [← hhalf, hxi, norm_div, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    have hstep : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) :=
      mul_le_mul hprod hL (norm_nonneg _) (by positivity)
    linarith
  have h1' : (1:ℝ) ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) := by linarith
  have hsq : (0:ℝ) ≤ s.im ^ 2 := sq_nonneg _
  have hlt : (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi))
      < (1 + s.im ^ 2) * (1 / 26) := by
    refine mul_lt_mul_of_pos_left const_lt ?_
    linarith
  have ht2 : (25:ℝ) < s.im ^ 2 := by linarith
  nlinarith [sq_abs s.im, abs_nonneg s.im]

end Cvs.ZeroFree
