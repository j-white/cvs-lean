import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The last integral the prime channel needs
-/

namespace Cvs.Moments

open Real intervalIntegral

/-- The antiderivative of `e^{γs}cos(ωs + ψ)`. -/
noncomputable def expCosAnti (γ ω ψ : ℝ) (s : ℝ) : ℝ :=
  Real.exp (γ * s) * (γ * Real.cos (ω * s + ψ) + ω * Real.sin (ω * s + ψ)) / (γ ^ 2 + ω ^ 2)

/-- **It differentiates back.**  The cross terms `γω·sin` cancel and the
denominator is exactly what is left. -/
theorem hasDerivAt_expCos {γ ω : ℝ} (h : γ ^ 2 + ω ^ 2 ≠ 0) (ψ s : ℝ) :
    HasDerivAt (expCosAnti γ ω ψ) (Real.exp (γ * s) * Real.cos (ω * s + ψ)) s := by
  have hlin : HasDerivAt (fun t : ℝ => ω * t + ψ) ω s := by
    simpa using ((hasDerivAt_id s).const_mul ω).add_const ψ
  have hc : HasDerivAt (fun t : ℝ => Real.cos (ω * t + ψ))
      (-Real.sin (ω * s + ψ) * ω) s := (Real.hasDerivAt_cos _).comp s hlin
  have hs : HasDerivAt (fun t : ℝ => Real.sin (ω * t + ψ))
      (Real.cos (ω * s + ψ) * ω) s := (Real.hasDerivAt_sin _).comp s hlin
  have he0 : HasDerivAt (fun t : ℝ => γ * t) γ s := by
    simpa using (hasDerivAt_id s).const_mul γ
  have he : HasDerivAt (fun t : ℝ => Real.exp (γ * t)) (Real.exp (γ * s) * γ) s := he0.exp
  have hg : HasDerivAt (fun t : ℝ => γ * Real.cos (ω * t + ψ) + ω * Real.sin (ω * t + ψ))
      (γ * (-Real.sin (ω * s + ψ) * ω) + ω * (Real.cos (ω * s + ψ) * ω)) s :=
    (hc.const_mul γ).add (hs.const_mul ω)
  have hmul := (he.mul hg).div_const (γ ^ 2 + ω ^ 2)
  have hd : ((Real.exp (γ * s) * γ)
        * (γ * Real.cos (ω * s + ψ) + ω * Real.sin (ω * s + ψ))
      + Real.exp (γ * s)
        * (γ * (-Real.sin (ω * s + ψ) * ω) + ω * (Real.cos (ω * s + ψ) * ω)))
      / (γ ^ 2 + ω ^ 2)
      = Real.exp (γ * s) * Real.cos (ω * s + ψ) := by
    field_simp
    ring
  rw [hd] at hmul
  exact hmul

/-- **The integral, in closed form.** -/
theorem integral_exp_cos {γ ω : ℝ} (h : γ ^ 2 + ω ^ 2 ≠ 0) (ψ A B : ℝ) :
    (∫ s in A..B, Real.exp (γ * s) * Real.cos (ω * s + ψ))
      = expCosAnti γ ω ψ B - expCosAnti γ ω ψ A := by
  have hcont : IntervalIntegrable
      (fun s : ℝ => Real.exp (γ * s) * Real.cos (ω * s + ψ)) MeasureTheory.volume A B := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_expCos h ψ s) hcont

end Cvs.Moments
