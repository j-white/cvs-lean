import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The real-line integral of a decaying holomorphic function on the upper half-plane vanishes

If `F` is holomorphic on `Im z > 0`, continuous on `Im z ≥ 0` and `|F z| (1 + |z|²) ≤ C` there, then `∫_ℝ F = 0`:
the Cauchy–Goursat identity on `[−R, R] × [0, R]`, whose top and sides are `O(1/R)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral
open Complex (I)

namespace Cvs.Upstream.UpperHalfPlaneIntegralVanishes

theorem norm_le_of_decay {F : ℂ → ℂ} {C R : ℝ} (hR : 0 < R)
    (hb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ * (1 + ‖z‖ ^ 2) ≤ C) {z : ℂ} (hz : 0 ≤ z.im) (hzR : R ≤ ‖z‖) :
    ‖F z‖ ≤ C / R ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : R ^ 2 ≤ 1 + ‖z‖ ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (hb z hz)

/-- **Vanishing real-line integral** of a function holomorphic on the upper half-plane with `O(1/|z|²)` decay. -/
theorem integral_eq_zero_of_decay {F : ℂ → ℂ} {C : ℝ}
    (hc : ContinuousOn F {z : ℂ | 0 ≤ z.im}) (hd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ * (1 + ‖z‖ ^ 2) ≤ C) :
    ∫ x : ℝ, F x = 0 := by
  have hcr : Continuous fun x : ℝ => F x :=
    hc.comp_continuous Complex.continuous_ofReal (fun x => by simp)
  have hint : Integrable fun x : ℝ => F x := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hcr.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have := hb x (by simp)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact this
  have hlim := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hbound : ∀ R : ℝ, 0 < R → ‖∫ x in -R..R, F x‖ ≤ 4 * C / R := by
    intro R hR
    have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F
      (-R : ℂ) (R + R * I) (hc.mono fun z hz => by
        rw [Complex.mem_reProdIm] at hz
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.neg_im, neg_zero] at hz
        rw [uIcc_of_le hR.le] at hz
        exact hz.2.1)
      (hd.mono fun z hz => by
        rw [Complex.mem_reProdIm] at hz
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.neg_im, neg_zero,
          min_eq_left hR.le, max_eq_right hR.le] at hz
        exact hz.2.1)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.neg_im, neg_zero, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.ofReal_im, sub_zero,
      Complex.ofReal_zero, zero_mul] at hrect
    have htop : ‖∫ x in -R..R, F (x + R * I)‖ ≤ C / R ^ 2 * |R - -R| := by
      refine norm_integral_le_of_norm_le_const fun x _ => norm_le_of_decay hR hb (by simp [hR.le]) ?_
      have := Complex.abs_im_le_norm ((x : ℂ) + R * I)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add, abs_of_pos hR] at this
      exact this
    have hside : ∀ s : ℝ, |s| = R → ‖∫ y in (0 : ℝ)..R, F (s + y * I)‖ ≤ C / R ^ 2 * |R - 0| := by
      intro s hs
      refine norm_integral_le_of_norm_le_const fun y hy => norm_le_of_decay hR hb ?_ ?_
      · rw [uIoc_of_le hR.le] at hy
        simpa using hy.1.le
      · have := Complex.abs_re_le_norm ((s : ℂ) + y * I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
          Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, hs] at this
        exact this
    have e : (∫ x in -R..R, F x) = (∫ x in -R..R, F (x + R * I)) -
        I • (∫ y in (0 : ℝ)..R, F (R + y * I)) + I • (∫ y in (0 : ℝ)..R, F (-R + y * I)) := by
      push_cast at hrect
      linear_combination hrect
    rw [e]
    have h1 := hside R (abs_of_pos hR)
    have h2 := hside (-R) (by rw [abs_neg, abs_of_pos hR])
    push_cast at h2
    have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hb 0 (by simp))
    calc _ ≤ ‖∫ x in -R..R, F (x + R * I)‖ + ‖I • ∫ y in (0 : ℝ)..R, F (R + y * I)‖ +
          ‖I • ∫ y in (0 : ℝ)..R, F (-R + y * I)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ C / R ^ 2 * |R - -R| + C / R ^ 2 * |R - 0| + C / R ^ 2 * |R - 0| := by
          rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
          gcongr
      _ = 4 * C / R := by
          rw [sub_neg_eq_add, sub_zero, abs_of_pos (by linarith), abs_of_pos hR]
          field_simp
          ring
  have h0 : Tendsto (fun R : ℝ => ∫ x in -R..R, F x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 4 * C)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with R hR using hbound R hR
  exact tendsto_nhds_unique hlim h0

end Cvs.Upstream.UpperHalfPlaneIntegralVanishes

end
