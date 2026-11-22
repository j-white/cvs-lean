import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.FirstPoleContourShift
import Cvs.Zeta.ExplicitFormula.PoleResidue
import Cvs.Zeta.ExplicitFormula.PoleTermsCancelCritical
import Cvs.Zeta.ExplicitFormula.ResidueAssembled

/-!
# The pole channel, evaluated

`an earlier result` bounded the pole channel below and measured the bound at 68× the true value with the
wrong sign.
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- On the critical line the two pole channels sum to something with zero real
part — `PoleTermsCancelCritical` pointwise, integrated. -/
theorem re_poleSum_line_eq_zero {h : ℂ → ℂ} {ρ : ℝ → ℝ} (hd : Differentiable ℂ h) {A : ℝ}
    (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) :
    ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (1 / 2 + (y : ℝ) * I))
        + ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)).re = 0 := by
  have hcast : (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  have h1 : Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (1 / 2 + (y : ℝ) * I)) := by
    have hh := Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.integrable_line hd hA hdec (c := (1 : ℝ) / 2) le_rfl (by norm_num)
    rwa [hcast] at hh
  have h2 : Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)) := by
    have hh := Cvs.Zeta.ExplicitFormula.ResidueAssembled.integrable_poleTwo_line hd hA hdec (c := (1 / 2 : ℝ)) le_rfl (by norm_num)
      (by rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) from by ring, abs_neg]; norm_num)
    simpa only [Cvs.Detection.cast_half] using hh
  rw [← integral_add h1 h2]
  have hre : (∫ y : ℝ, (Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (1 / 2 + (y : ℝ) * I)
        + Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)).re)
      = (∫ y : ℝ, (Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (1 / 2 + (y : ℝ) * I)
        + Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I))).re := integral_re (h1.add h2)
  rw [← hre]
  simp_rw [Cvs.Detection.re_poleSum_critical hrho]
  exact integral_zero ℝ ℝ

/-- **The pole channel, evaluated.**  `2π` times the explicit formula's main term. -/
theorem pole_channel_eq {h : ℂ → ℂ} {ρ : ℝ → ℝ} (hd : Differentiable ℂ h) {A : ℝ}
    (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) :
    ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (2 + (y : ℝ) * I))
        + ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I)).re
      = 2 * π * (Cvs.Zeta.ofCritical h 1).re := by
  have hres := Cvs.Detection.poleTwo_residue hd hA hdec
  have hP2 : (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
      = (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I))
        + ((2 * π : ℝ) : ℂ) * Cvs.Zeta.ofCritical h 1 := by
    rw [← hres]; ring
  rw [Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.contour_shift hd hA hdec, hP2, ← add_assoc, Complex.add_re,
    re_poleSum_line_eq_zero hd hA hdec hrho, zero_add, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end Cvs.Detection
