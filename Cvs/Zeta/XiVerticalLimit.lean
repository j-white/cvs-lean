import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical
import Cvs.Zeta.ZetaLowerBound

/-!
# The vertical side converges

`Cvs.Zeta.XiHorizontal` shows the horizontal sides of the rung-7 contour vanish.
-/

open Complex Real MeasureTheory

namespace Cvs.Zeta

/-- `ξ` does not vanish on the line `Re s = 2`. -/
theorem riemannXi_ne_zero_of_re_eq_two {s : ℂ} (hs : s.re = 2) : riemannXi s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  rw [Ne, riemannXi_eq_zero_iff_riemannZeta (by rw [hs]; norm_num) hs1]
  exact riemannZeta_ne_zero_of_re_eq_two hs

/-- `ξ'/ξ` is continuous along the line `Re s = 2`. -/
theorem continuous_logDeriv_riemannXi_vertical :
    Continuous fun y : ℝ => logDeriv riemannXi ((2 : ℂ) + y * I) := by
  have hline : ∀ y : ℝ, (((2 : ℂ) + y * I)).re = 2 := by intro y; simp
  have hderiv : Continuous (deriv riemannXi) :=
    continuous_iff_continuousAt.mpr fun x =>
      ((analyticOnNhd_riemannXi.deriv) x (Set.mem_univ x)).continuousAt
  have hpath : Continuous fun y : ℝ => ((2 : ℂ) + y * I) := by fun_prop
  simp only [logDeriv_apply]
  exact (hderiv.comp hpath).div ((differentiable_riemannXi.continuous).comp hpath)
    fun y => riemannXi_ne_zero_of_re_eq_two (hline y)

/-- The vertical integrand is dominated by `2CA/(1+y²)`, for **any** `f` that is `O(log|y|)` on
the line. -/
theorem norm_vline_integrand_le {f φ : ℂ → ℂ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlog : ∀ s : ℂ, s.re = 2 → 2 ≤ |s.im| → ‖f s‖ ≤ C * (1 + Real.log (2 + |s.im|)))
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3)
    {y : ℝ} (hy : 2 ≤ |y|) :
    ‖f ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)‖
      ≤ (2 * C * A) * (1 + y ^ 2)⁻¹ := by
  have him : (((2 : ℂ) + y * I)).im = y := by simp
  have hre : (((2 : ℂ) + y * I)).re = 2 := by simp
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  have h1 : ‖f ((2 : ℂ) + y * I)‖ ≤ C * (1 + Real.log (2 + |y|)) := by
    have := hlog ((2 : ℂ) + y * I) hre (by rw [him]; exact hy)
    rwa [him] at this
  have h2 : ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3 := hφ y
  have hlogle : Real.log (2 + |y|) ≤ 1 + |y| := by
    have := Real.log_le_sub_one_of_pos (x := 2 + |y|) (by linarith)
    linarith
  have hnum : 1 + Real.log (2 + |y|) ≤ 2 * (1 + |y|) := by linarith
  have hpos : (0 : ℝ) < (1 + |y|) ^ 3 := by positivity
  have hCA : (0 : ℝ) ≤ C * A := mul_nonneg hC hA
  have hkey : C * (1 + Real.log (2 + |y|)) * A ≤ 2 * C * A * (1 + |y|) := by
    nlinarith [hCA, hnum, habs]
  have hstep : C * (1 + Real.log (2 + |y|)) * (A / (1 + |y|) ^ 3)
      ≤ 2 * C * A / (1 + |y|) ^ 2 := by
    calc C * (1 + Real.log (2 + |y|)) * (A / (1 + |y|) ^ 3)
        = C * (1 + Real.log (2 + |y|)) * A / (1 + |y|) ^ 3 := by ring
      _ ≤ 2 * C * A * (1 + |y|) / (1 + |y|) ^ 3 := by gcongr
      _ = 2 * C * A / (1 + |y|) ^ 2 := by
          have hne : (1 : ℝ) + |y| ≠ 0 := by positivity
          field_simp
  have hsq : (1 : ℝ) + y ^ 2 ≤ (1 + |y|) ^ 2 := by
    have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    nlinarith [habs]
  have hfin : 2 * C * A / (1 + |y|) ^ 2 ≤ (2 * C * A) * (1 + y ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hsq
  rw [norm_mul]
  have hlog0 : (0 : ℝ) ≤ Real.log (2 + |y|) :=
    Real.log_nonneg (by linarith)
  refine le_trans (le_trans (mul_le_mul h1 h2 (norm_nonneg _)
    (mul_nonneg hC (by linarith))) hstep) hfin

/-- **Any `O(log|y|)` factor is integrable against a cubically decaying test function on the
line `Re s = 2`.**  All four summands of `ξ'/ξ` qualify — see `Cvs.Zeta.XiVerticalSplit`. -/
theorem integrableOn_vline {f φ : ℂ → ℂ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfc : ContinuousOn (fun y : ℝ => f ((2 : ℂ) + y * I)) {y : ℝ | 2 ≤ |y|})
    (hlog : ∀ s : ℂ, s.re = 2 → 2 ≤ |s.im| → ‖f s‖ ≤ C * (1 + Real.log (2 + |s.im|)))
    (hφc : Continuous φ) (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    IntegrableOn (fun y : ℝ => f ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      {y : ℝ | 2 ≤ |y|} := by
  have hmeas : MeasurableSet {y : ℝ | 2 ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hpath : Continuous fun y : ℝ => ((2 : ℂ) + y * I) := by fun_prop
  have hφline : Continuous fun y : ℝ => φ ((2 : ℂ) + y * I) := hφc.comp hpath
  have hcont : ContinuousOn (fun y : ℝ => f ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      {y : ℝ | 2 ≤ |y|} := hfc.mul hφline.continuousOn
  have hdom : Integrable (fun y : ℝ => (2 * C * A) * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom.restrict (hcont.aestronglyMeasurable hmeas) ?_
  refine (ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  exact norm_vline_integrand_le hA hC hlog hφ hy

/-- **The vertical side converges.** On the line `Re s = 2` the integrand `(ξ'/ξ)·φ` is integrable
outside `|y| ≤ 2`, for any continuous test function with cubic decay in the imaginary
direction. -/
theorem integrableOn_vertical {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    IntegrableOn (fun y : ℝ =>
        logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      {y : ℝ | 2 ≤ |y|} := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_riemannXi_le_re_two
  exact integrableOn_vline hA hC0 continuous_logDeriv_riemannXi_vertical.continuousOn hC hφc hφ

end Cvs.Zeta
