import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Cvs.Zeta.ExplicitFormula.PoleFactorRealPart
import Cvs.Zeta.ExplicitFormula.VerticalInverseIntegral

/-!
# The pole factor's vertical integral, both signs, in full

The residue argument needs `∫_{−R}^{R} dy/(a+iy)` at *two* verticals: `a = 1` at `Re z = 2`,
and `a = −½` at `Re z = ½`.
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory Filter
open scoped Real Topology

theorem im_inv_line (a y : ℝ) :
    ((((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).im = -y * (a ^ 2 + y ^ 2)⁻¹ := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp
  ring

/-- The imaginary part is odd, so it integrates away over a symmetric interval. -/
theorem im_integral_inv_line {a : ℝ} (ha : a ≠ 0) (R : ℝ) :
    (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).im = 0 := by
  have hcont : Continuous (fun y : ℝ => (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y hz => ?_
    have hre : (((a : ℝ) : ℂ) + (y : ℝ) * I).re = a := by simp
    rw [hz] at hre
    simp at hre
    exact ha hre.symm
  have hint : IntervalIntegrable (fun y : ℝ => (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      volume (-R) R := hcont.intervalIntegrable _ _
  have him : (∫ y in (-R)..R, ((((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).im)
      = (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).im :=
    intervalIntegral.intervalIntegral_im hint
  rw [← him]
  simp_rw [im_inv_line]
  refine Cvs.Detection.integral_odd_eq_zero (fun x => ?_) R
  have hsq : (-x) ^ 2 = x ^ 2 := by ring
  rw [hsq]
  ring

/-- **The pole factor's vertical integral, `a > 0`.** -/
theorem integral_inv_line_pos {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      = ((2 * Real.arctan (R / a) : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
    exact Cvs.Detection.re_integral_inv_line ha R
  · rw [Complex.ofReal_im]
    exact im_integral_inv_line (ne_of_gt ha) R

/-- **The pole factor's vertical integral, `a < 0`** — the same magnitude with the
opposite sign.  That sign flip is the residue. -/
theorem integral_inv_line_neg {a : ℝ} (ha : a < 0) (R : ℝ) :
    (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      = ((-(2 * Real.arctan (R / -a)) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < -a := by linarith
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
    have hint : IntervalIntegrable (fun y : ℝ => (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
        volume (-R) R := by
      refine Continuous.intervalIntegrable ?_ _ _
      refine Continuous.inv₀ (by fun_prop) fun y hz => ?_
      have hre : (((a : ℝ) : ℂ) + (y : ℝ) * I).re = a := by simp
      rw [hz] at hre
      simp at hre
      linarith
    have hre : (∫ y in (-R)..R, ((((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re)
        = (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re :=
      intervalIntegral.intervalIntegral_re hint
    rw [← hre]
    simp_rw [Cvs.Detection.re_inv_line]
    have hsq : ∀ y : ℝ, a ^ 2 + y ^ 2 = (-a) ^ 2 + y ^ 2 := fun y => by ring
    simp_rw [hsq]
    rw [intervalIntegral.integral_const_mul, Cvs.Detection.integral_inv_sq_add_sq hpos]
    have hane : a ≠ 0 := ne_of_lt ha
    field_simp
  · rw [Complex.ofReal_im]
    exact im_integral_inv_line (ne_of_lt ha) R

theorem tendsto_arctan_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => Real.arctan (R / a)) atTop (𝓝 (π / 2)) :=
  (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1.comp
    (Filter.Tendsto.atTop_div_const ha tendsto_id)

/-- `→ π` on the right vertical. -/
theorem tendsto_integral_inv_line_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      atTop (𝓝 ((π : ℝ) : ℂ)) := by
  have hh := ((tendsto_arctan_div ha).const_mul (2 : ℝ)).ofReal
  have harg : (2 : ℝ) * (π / 2) = π := by ring
  rw [harg] at hh
  exact Tendsto.congr (fun R => (integral_inv_line_pos ha R).symm) hh

/-- `→ −π` on the left vertical.  The difference `2π` is the residue's
coefficient. -/
theorem tendsto_integral_inv_line_neg {a : ℝ} (ha : a < 0) :
    Tendsto (fun R : ℝ => ∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      atTop (𝓝 (-(π : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < -a := by linarith
  have hh := (((tendsto_arctan_div hpos).const_mul (2 : ℝ)).neg).ofReal
  have harg : -((2 : ℝ) * (π / 2)) = -π := by ring
  rw [harg] at hh
  refine Tendsto.congr (fun R => (integral_inv_line_neg ha R).symm) ?_
  simpa using hh

end Cvs.Detection
