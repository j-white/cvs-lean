import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CriticalLineDensity
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum

/-!
# On the critical line the compactly supported test is a modulus squared
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- Conjugation passes through an interval integral. -/
theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (starRingEnd ℂ) (∫ x in a..b, f x) = ∫ x in a..b, (starRingEnd ℂ) (f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
    intervalIntegral.intervalIntegral_eq_integral_uIoc]
  split_ifs <;> simp [integral_conj]

/-- For a real test the transform at `−y` is the conjugate of the transform at `y`. -/
theorem windowTransform_conj (L : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    (starRingEnd ℂ) (Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (y : ℝ))
      = Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (-(y : ℝ)) := by
  rw [Cvs.Detection.windowTransform, Cvs.Detection.windowTransform, intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  apply Complex.ext <;> simp

/-- **The density is a modulus squared.** -/
theorem sqTransform_real (L : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ)) (y : ℝ)
      = ((‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (y : ℝ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Cvs.Detection.sqTransform, ← windowTransform_conj, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

/-- **On the critical line, the compactly supported test is `‖Ŵ(y)‖²`.** -/
theorem ofCritical_sqTransform_half (L : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ)))
        (1 / 2 + (y : ℝ) * I)
      = ((‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (y : ℝ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Cvs.Detection.ofCritical_half, sqTransform_real]

end Cvs.Detection
