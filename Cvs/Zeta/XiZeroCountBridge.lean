import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues

/-!
# Transferring the zero count from `ζ` to `ξ`

`Cvs.Zeta.ZetaZeroCount` proves `O(log T)` zeros of `ζ` in the disc `|s − (2+iT)| ≤ 9/4`.
-/

open Complex Real Set Metric

namespace Cvs.Zeta

/-- `Gammaℝ` has no zeros off the real axis: `π^{-s/2}` never vanishes and the poles
of `Γ(s/2)` are all real. -/
theorem gammaR_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ]
  refine mul_ne_zero ?_ ?_
  · refine Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.mpr ?_
    · intro h
      rw [neg_div, neg_eq_zero, div_eq_zero_iff] at h
      rcases h with h | h
      · exact hs (by rw [h]; simp)
      · norm_num at h
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · refine Complex.Gamma_ne_zero fun m hm => ?_
    have : (s / 2).im = 0 := by rw [hm]; simp
    simp at this
    exact hs this

theorem isOpen_im_ne_zero : IsOpen {s : ℂ | s.im ≠ 0} :=
  isOpen_compl_iff.mpr (isClosed_eq Complex.continuous_im continuous_const)

theorem ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h; exact hs (by rw [h]; simp)

theorem ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := by
  intro h; exact hs (by rw [h]; simp)

end Cvs.Zeta
