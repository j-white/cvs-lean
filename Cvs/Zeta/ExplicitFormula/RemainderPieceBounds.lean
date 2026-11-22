import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Zeta.ExplicitFormula.ExpCosIntegral

/-!
# Every piece of `R`, bounded
-/

namespace Cvs.Enclosure

/-- **Cauchy–Schwarz on the antiderivative's numerator.**  The slack is
`(γ·sin θ − ω·cos θ)²`. -/
theorem abs_lin_comb_le (γ ω θ : ℝ) :
    |γ * Real.cos θ + ω * Real.sin θ| ≤ Real.sqrt (γ ^ 2 + ω ^ 2) := by
  have hpy : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hsq : (γ * Real.cos θ + ω * Real.sin θ) ^ 2 ≤ γ ^ 2 + ω ^ 2 := by
    nlinarith [sq_nonneg (γ * Real.sin θ - ω * Real.cos θ), hpy]
  calc |γ * Real.cos θ + ω * Real.sin θ|
      = Real.sqrt ((γ * Real.cos θ + ω * Real.sin θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (γ ^ 2 + ω ^ 2) := Real.sqrt_le_sqrt hsq

/-- **Every `expCosAnti` evaluation, bounded.**  The denominator loses a full power of
its root to Cauchy–Schwarz. -/
theorem abs_expCosAnti_le {γ ω : ℝ} (h : γ ^ 2 + ω ^ 2 ≠ 0) (ψ s : ℝ) :
    |Cvs.Moments.expCosAnti γ ω ψ s| ≤ Real.exp (γ * s) / Real.sqrt (γ ^ 2 + ω ^ 2) := by
  have hpos : (0 : ℝ) < γ ^ 2 + ω ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have hsq : (0 : ℝ) < Real.sqrt (γ ^ 2 + ω ^ 2) := Real.sqrt_pos.mpr hpos
  have hmul : Real.sqrt (γ ^ 2 + ω ^ 2) * Real.sqrt (γ ^ 2 + ω ^ 2) = γ ^ 2 + ω ^ 2 :=
    Real.mul_self_sqrt (le_of_lt hpos)
  have hlin := abs_lin_comb_le γ ω (ω * s + ψ)
  have hexp : (0 : ℝ) < Real.exp (γ * s) := Real.exp_pos _
  unfold Cvs.Moments.expCosAnti
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_pos hexp, div_le_iff₀ hpos,
    div_mul_eq_mul_div, le_div_iff₀ hsq]
  calc Real.exp (γ * s) * |γ * Real.cos (ω * s + ψ) + ω * Real.sin (ω * s + ψ)|
        * Real.sqrt (γ ^ 2 + ω ^ 2)
      ≤ Real.exp (γ * s) * Real.sqrt (γ ^ 2 + ω ^ 2) * Real.sqrt (γ ^ 2 + ω ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hsq)
        exact mul_le_mul_of_nonneg_left hlin (le_of_lt hexp)
    _ = Real.exp (γ * s) * (γ ^ 2 + ω ^ 2) := by rw [mul_assoc, hmul]

end Cvs.Enclosure
