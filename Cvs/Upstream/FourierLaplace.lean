import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Support

/-
Copyright (c) 2026 Jesse White. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse White
-/

/-!
# The Fourier–Laplace transform of a compactly supported function

For `g : ℝ → ℂ` and `w : ℂ`, `fourierLaplace g w = ∫ g(t) e^{iwt} dt`.
-/

open MeasureTheory Complex Metric

namespace FourierLaplace

-- prose-lint-allow: R7 an upstreaming restatement of an earlier result; the reference is provenance, not a dependency
/-!
# The Fourier–Laplace transform of a compactly supported function is entire

This is the one analytic input the `pathlaw` explicit formula needs that Mathlib does not
have.
-/

/-- The Fourier–Laplace transform, as an integral over the whole line. -/
noncomputable def fourierLaplace (g : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ t : ℝ, g t * Complex.exp (Complex.I * w * (t : ℂ))

/-- `‖exp (I w t)‖ = exp (-(t * w.im))`. -/
theorem norm_exp_I_mul (w : ℂ) (t : ℝ) :
    ‖Complex.exp (Complex.I * w * (t : ℂ))‖ = Real.exp (-(t * w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- A compactly supported integrable function is integrable against the kernel. -/
theorem integrable_mul_kernel {g : ℝ → ℂ} (hgi : Integrable g)
    (hsupp : HasCompactSupport g) (w : ℂ) :
    Integrable (fun t : ℝ => g t * Complex.exp (Complex.I * w * (t : ℂ))) := by
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : ℝ)
  have hR0 : ∀ t : ℝ, t ∉ Metric.closedBall (0 : ℝ) R → g t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hm => ht (hR hm)
  refine (hgi.norm.const_mul (Real.exp (|R| * |w.im|))).mono'
    (hgi.aestronglyMeasurable.mul (by fun_prop))
    (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Metric.closedBall (0 : ℝ) R
  · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    rw [norm_mul, norm_exp_I_mul]
    have hexp : Real.exp (-(t * w.im)) ≤ Real.exp (|R| * |w.im|) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -(t * w.im) ≤ |t| * |w.im| := by
        calc -(t * w.im) ≤ |t * w.im| := neg_le_abs _
          _ = |t| * |w.im| := abs_mul t w.im
      have h3 : |t| ≤ |R| := le_trans ht (le_abs_self R)
      nlinarith [abs_nonneg w.im, abs_nonneg t]
    calc ‖g t‖ * Real.exp (-(t * w.im))
        ≤ ‖g t‖ * Real.exp (|R| * |w.im|) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = Real.exp (|R| * |w.im|) * ‖g t‖ := by ring
  · rw [hR0 t ht]
    simp

theorem differentiable_fourierLaplace_of_integrable {g : ℝ → ℂ} (hgi : Integrable g)
    (hsupp : HasCompactSupport g) :
    Differentiable ℂ (fourierLaplace g) := by
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : ℝ)
  have hR0 : ∀ t : ℝ, t ∉ Metric.closedBall (0 : ℝ) R → g t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hm => ht (hR hm)
  intro w₀
  set M : ℝ := |w₀.im| + 1 with hM
  set C : ℝ := Real.exp (|R| * M) with hC
  -- the dominating function
  set bound : ℝ → ℝ := fun t => ‖g t‖ * |t| * C with hbound
  have hboundint : Integrable bound := by
    refine (hgi.norm.const_mul (|R| * C)).mono'
      ((hgi.norm.aestronglyMeasurable.mul (by fun_prop)).mul (by fun_prop))
      (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Metric.closedBall (0 : ℝ) R
    · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
      rw [hbound, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : |t| ≤ |R| := le_trans ht (le_abs_self R)
      have hCnn : (0:ℝ) ≤ C := (Real.exp_pos _).le
      have hgn : (0:ℝ) ≤ ‖g t‖ := norm_nonneg _
      calc ‖g t‖ * |t| * C ≤ ‖g t‖ * |R| * C := by gcongr
        _ = |R| * C * ‖g t‖ := by ring
    · simp [hbound, hR0 t ht]
  have hFint : ∀ w : ℂ, Integrable (fun t : ℝ => g t * Complex.exp (Complex.I * w * (t : ℂ))) :=
    fun w => integrable_mul_kernel hgi hsupp w
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable
      (fun t : ℝ => g t * Complex.exp (Complex.I * w * (t : ℂ))) volume :=
    fun w => (hFint w).aestronglyMeasurable
  have hderiv : ∀ (t : ℝ) (w : ℂ),
      HasDerivAt (fun w : ℂ => g t * Complex.exp (Complex.I * w * (t : ℂ)))
        (g t * (Complex.exp (Complex.I * w * (t : ℂ)) * (Complex.I * (t : ℂ)))) w := by
    intro t w
    have h1 : HasDerivAt (fun w : ℂ => Complex.I * w * (t : ℂ)) (Complex.I * (t : ℂ)) w := by
      simpa using ((hasDerivAt_id w).const_mul Complex.I).mul_const ((t : ℂ))
    exact (h1.cexp).const_mul (g t)
  have hbd : ∀ᵐ t : ℝ, ∀ w ∈ ball w₀ 1,
      ‖g t * (Complex.exp (Complex.I * w * (t : ℂ)) * (Complex.I * (t : ℂ)))‖ ≤ bound t := by
    filter_upwards with t w hw
    by_cases ht : t ∈ Metric.closedBall (0 : ℝ) R
    · have him : |w.im| ≤ M := by
        have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
          simpa using Complex.abs_im_le_norm (w - w₀)
        have h2 : ‖w - w₀‖ < 1 := by simpa [Complex.dist_eq] using hw
        have := abs_sub_abs_le_abs_sub w.im w₀.im
        rw [hM]
        linarith [abs_nonneg (w.im - w₀.im)]
      have htR : |t| ≤ R := by simpa [Real.dist_eq] using ht
      have hexp : ‖Complex.exp (Complex.I * w * (t : ℂ))‖ ≤ C := by
        rw [norm_exp_I_mul, hC]
        apply Real.exp_le_exp.mpr
        have : -(t * w.im) ≤ |t| * |w.im| := by
          calc -(t * w.im) ≤ |t * w.im| := neg_le_abs _
            _ = |t| * |w.im| := abs_mul t w.im
        calc -(t * w.im) ≤ |t| * |w.im| := this
          _ ≤ |R| * M := by
              apply mul_le_mul _ him (abs_nonneg _) (abs_nonneg _)
              exact htR.trans (le_abs_self R)
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, hbound]
      calc ‖g t‖ * (‖Complex.exp (Complex.I * w * (t : ℂ))‖ * |t|)
          ≤ ‖g t‖ * (C * |t|) := by
            gcongr
        _ = ‖g t‖ * |t| * C := by ring
    · simp [hR0 t ht, hbound]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w : ℂ => fun t : ℝ => g t * Complex.exp (Complex.I * w * (t : ℂ)))
    (F' := fun w : ℂ => fun t : ℝ =>
      g t * (Complex.exp (Complex.I * w * (t : ℂ)) * (Complex.I * (t : ℂ))))
    (bound := bound) (ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun w => hmeas w) (hFint w₀)
    (hgi.aestronglyMeasurable.mul (by fun_prop)) hbd hboundint
    (Filter.Eventually.of_forall fun t w _ => hderiv t w)
  exact hmain.2.differentiableAt

/-- **Evenness.**  The transform of an even test is even — which is the last of
`Cvs.Zeta.guinand_weil_classical`'s four hypotheses, and the one the
self-convolution supplies for free. -/
theorem fourierLaplace_even {g : ℝ → ℂ} (heven : ∀ t : ℝ, g (-t) = g t) (w : ℂ) :
    fourierLaplace g (-w) = fourierLaplace g w := by
  rw [fourierLaplace, fourierLaplace, ← MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => g t * Complex.exp (Complex.I * w * (t : ℂ)))]
  refine congrArg (MeasureTheory.integral _) (funext fun t => ?_)
  rw [heven t]
  congr 2
  push_cast
  ring

end FourierLaplace
