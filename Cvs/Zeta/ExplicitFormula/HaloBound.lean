import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal
import Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand

/-!
# The halo bound, for any admissible test with a nonnegative density

`Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift` generalised the contour shift over the test.
-/

namespace Cvs.Zeta.ExplicitFormula.HaloBound
open Cvs.Detection

open Complex MeasureTheory
open scoped Real

variable {h : ℂ → ℂ} {ρ : ℝ → ℝ}

/-- The real part of the integrand on the line is `archScore · ρ`. -/
theorem re_archIntegrand_critical
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) (y : ℝ) :
    (Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)).re = Cvs.Detection.archScore y * ρ y := by
  rw [Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand, hrho y, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Cvs.Detection.archScore, show (1 : ℂ) / 2 + I * (y : ℝ) = 1 / 2 + (y : ℝ) * I from by ring]
  ring

/-- The integrand on the line is conjugate-symmetric, so the integral is real. -/
theorem archIntegrand_conj
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ))
    (heven : ∀ y : ℝ, ρ (-y) = ρ y) (y : ℝ) :
    Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + ((-y : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) (Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)) := by
  rw [Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand, map_mul, hrho y, hrho (-y), heven y,
    ← Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.conj_half_add, Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.logDeriv_gammaR_conj (Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.half_add_re_pos y),
    Complex.conj_ofReal]

/-- **The channel on the line is the real pairing `∫ archScore · ρ`.** -/
theorem arch_line_integral_real {A : ℝ} (hd : Differentiable ℂ h) (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ))
    (heven : ∀ y : ℝ, ρ (-y) = ρ y) :
    (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I))
      = ((∫ y : ℝ, Cvs.Detection.archScore y * ρ y : ℝ) : ℂ) := by
  have hcast : (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  have hint : Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)) := by
    have hh := Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.integrable_line hd hA hdec (c := (1 : ℝ) / 2) le_rfl (by norm_num)
    rwa [hcast] at hh
  have hsym : (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I))
      = (starRingEnd ℂ) (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)) := by
    calc (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I))
        = ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + ((-y : ℝ) : ℂ) * I) :=
          (Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.integral_comp_neg _).symm
      _ = ∫ y : ℝ, (starRingEnd ℂ) (Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)) := by
          simp_rw [archIntegrand_conj hrho heven]
      _ = (starRingEnd ℂ) (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)) :=
          integral_conj
  have him : (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)).im = 0 :=
    Complex.conj_eq_iff_im.mp hsym.symm
  have hre : (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)).re
      = ∫ y : ℝ, Cvs.Detection.archScore y * ρ y := by
    have hh : (∫ y : ℝ, (Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)).re)
        = (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (1 / 2 + (y : ℝ) * I)).re := integral_re hint
    rw [← hh]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
      re_archIntegrand_critical hrho y)
  rw [← hre]
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im]; exact him

end Cvs.Zeta.ExplicitFormula.HaloBound
