import Mathlib
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.GenusOneSumAllZeros
import Cvs.Zeta.HadamardProduct.XiExceptionalSet
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ThetaDecay
import Cvs.Zeta.ZetaRealSegment

/-!
# The small-zero term vanishes, and the closed form is one sum
-/

noncomputable section

open Complex Set MeasureTheory Cvs.Zeta

namespace Cvs.ZeroFree

/-- The sharpened kernel bound: `e^{−πt} ≤ e^{1−π}·e^{−t}` on `t ≥ 1`, kept rather than
degraded. -/
theorem abs_evenKernel_sub_one_le' {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.evenKernel 0 t - 1| ≤ (4 * Real.exp (1 - Real.pi)) * Real.exp (-t) := by
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
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hhalf : Real.exp (-(Real.pi * t)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(Real.pi * t)) ≤ Real.exp (-1) := by
      refine Real.exp_le_exp.mpr ?_; nlinarith
    refine h1.trans ?_
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hpos : (0 : ℝ) < 1 - Real.exp (-Real.pi * t) := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring]; linarith
  have hpre : 2 / (1 - Real.exp (-Real.pi * t)) ≤ 4 := by
    rw [div_le_iff₀ hpos, show -Real.pi * t = -(Real.pi * t) by ring] at *
    linarith
  -- keep the `π`: `e^{-πt} ≤ e^{1-π} e^{-t}` for `t ≥ 1`
  have hkey : Real.exp (-Real.pi * t) ≤ Real.exp (1 - Real.pi) * Real.exp (-t) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc 2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t)
      ≤ 4 * Real.exp (-Real.pi * t) :=
        mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
    _ ≤ 4 * (Real.exp (1 - Real.pi) * Real.exp (-t)) := by
        exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = (4 * Real.exp (1 - Real.pi)) * Real.exp (-t) := by ring

theorem abs_cosKernel_sub_one_le' {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.cosKernel 0 t - 1| ≤ (4 * Real.exp (1 - Real.pi)) * Real.exp (-t) := by
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  exact abs_evenKernel_sub_one_le' ht

/-- The tail bound, with the constant as a parameter. -/
theorem norm_kernel_tail_le' {e : ℂ} (he : e.re ≤ 0) (C : ℝ) (hC : 0 ≤ C) (K : ℝ → ℝ)
    (hK : ∀ t : ℝ, 1 ≤ t → |K t - 1| ≤ C * Real.exp (-t)) :
    ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ e • (((K t : ℝ) : ℂ) - 1)‖ ≤ C * Real.exp (-1) := by
  have hint : IntegrableOn (fun t : ℝ => C * Real.exp (-t)) (Set.Ioi (1:ℝ)) := by
    have h := exp_neg_integrableOn_Ioi (1:ℝ) (b := 1) one_pos
    simp only [neg_mul, one_mul] at h
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
    calc (t : ℝ) ^ e.re * |K t - 1| ≤ 1 * (C * Real.exp (-t)) :=
          mul_le_mul hpow (hK t ht1) (abs_nonneg _) zero_le_one
      _ = C * Real.exp (-t) := by ring
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

/-- **`‖Λ₀‖ ≤ 4e^{−π}` on `−1 ≤ Re s ≤ 2`** — eight times sharper than `4/e`, and valid on a
wider strip, which is what covers the unit disc. -/
theorem norm_completedRiemannZeta₀_le_disc {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.exp (-Real.pi) := by
  rw [completedRiemannZeta₀_eq_Lambda0, Lambda0_zeta_eq_tails, norm_div]
  have hre : (s / 2).re = s.re / 2 := by simp
  have he1 : (s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, hre]; simp; linarith
  have he2 : ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, Complex.sub_re, hre]; simp; linarith
  have hC0 : (0:ℝ) ≤ 4 * Real.exp (1 - Real.pi) := by positivity
  have hA := norm_kernel_tail_le' he1 _ hC0 (HurwitzZeta.evenKernel 0)
    (fun t ht => abs_evenKernel_sub_one_le' ht)
  have hB := norm_kernel_tail_le' he2 _ hC0 (HurwitzZeta.cosKernel 0)
    (fun t ht => abs_cosKernel_sub_one_le' ht)
  have hsum : ‖(∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s / 2 - 1)
        • (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
      + ∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1)
        • (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1)‖
      ≤ (4 * Real.exp (1 - Real.pi)) * Real.exp (-1)
        + (4 * Real.exp (1 - Real.pi)) * Real.exp (-1) :=
    le_trans (norm_add_le _ _) (add_le_add hA hB)
  have hval : (4 * Real.exp (1 - Real.pi)) * Real.exp (-1) = 4 * Real.exp (-Real.pi) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hval] at hsum
  have h2pos : (0:ℝ) < ‖(2:ℂ)‖ := by norm_num
  rw [show ‖(2:ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- `4e^{−π} < ½`. -/
theorem four_exp_neg_pi_lt_half : 4 * Real.exp (-Real.pi) < 1 / 2 := by
  have h3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have h : Real.exp (-Real.pi) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
  have hx : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : (19:ℝ) < Real.exp 3 := by
    rw [h1]
    have hfac : Real.exp 1 ^ 3 - 19.683
        = (Real.exp 1 - 2.7) * (Real.exp 1 ^ 2 + 2.7 * Real.exp 1 + 7.29) := by ring
    have hp1 : 0 < Real.exp 1 - 2.7 := by linarith
    have hp2 : 0 < Real.exp 1 ^ 2 + 2.7 * Real.exp 1 + 7.29 := by positivity
    have hkey : 0 < Real.exp 1 ^ 3 - 19.683 := by rw [hfac]; exact mul_pos hp1 hp2
    linarith
  have hlt : Real.exp (-3) < 1 / 19 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 3) (by norm_num)]
    linarith
  linarith

/-- **`ξ` has no zero in the closed unit disc.** -/
theorem riemannXi_ne_zero_of_norm_le_one {s : ℂ} (hs : ‖s‖ ≤ 1) : riemannXi s ≠ 0 := by
  have hre1 : -1 ≤ s.re := by
    have := Complex.abs_re_le_norm s
    have h := abs_le.mp (le_trans this hs)
    exact h.1
  have hre2 : s.re ≤ 2 := by
    have := Complex.abs_re_le_norm s
    have h := abs_le.mp (le_trans this hs)
    linarith [h.2]
  have hL := norm_completedRiemannZeta₀_le_disc hre1 hre2
  have hs1 : ‖s - 1‖ ≤ 2 := by
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith
  have hxi : riemannXi s - 1 / 2 = s * (s - 1) * completedRiemannZeta₀ s / 2 := by
    rw [riemannXi]; ring
  have hbound : ‖riemannXi s - 1 / 2‖ ≤ 4 * Real.exp (-Real.pi) := by
    rw [hxi, norm_div, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    calc ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ 1 * 2 * (4 * Real.exp (-Real.pi)) := by
          refine mul_le_mul (mul_le_mul hs hs1 (norm_nonneg _) zero_le_one) hL
            (norm_nonneg _) (by positivity)
      _ = 4 * Real.exp (-Real.pi) * 2 := by ring
  intro hc
  rw [hc] at hbound
  have : ‖(0:ℂ) - 1/2‖ = 1/2 := by
    rw [zero_sub, norm_neg, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
  rw [this] at hbound
  linarith [four_exp_neg_pi_lt_half]

/-! ### The payoff -/

/-- **There are no small zeros.** -/
theorem smallS_eq_empty : Cvs.ZeroFree.smallS = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  rw [Cvs.ZeroFree.smallS, Set.Finite.mem_toFinset] at hu
  have hne : riemannXi u ≠ 0 := riemannXi_ne_zero_of_norm_le_one hu.1.le
  refine hu.2 ?_
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ u)]
  have hord : analyticOrderAt riemannXi u = 0 := by
    rw [analyticOrderAt_eq_zero]; exact Or.inr hne
  rw [hord]
  simp

theorem smallGenus_eq_zero (z : ℂ) : Cvs.ZeroFree.smallGenus z = 0 := by
  rw [Cvs.ZeroFree.smallGenus, smallS_eq_empty, Finset.sum_empty]

/-- **The closed form, final.**  One sum over the zeros, and nothing else. -/
theorem logDeriv_riemannXi_clean {z : ℂ} (hz : riemannXi z ≠ 0) :
    logDeriv riemannXi z - logDeriv riemannXi 0
      = ∑' n : zeroIndex riemannXi,
          (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n) := by
  rw [Cvs.ZeroFree.logDeriv_sub_logDeriv_zero hz, smallGenus_eq_zero, zero_add]

end Cvs.ZeroFree
