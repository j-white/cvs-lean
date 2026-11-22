import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# The transform of an exponential sum

`an earlier result` gave the transform of a single exponential.
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory
open scoped Real

theorem windowTransform_add (L : ℝ) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (ξ : ℂ) :
    Cvs.Detection.windowTransform L (fun s => f s + g s) ξ
      = Cvs.Detection.windowTransform L f ξ + Cvs.Detection.windowTransform L g ξ := by
  rw [Cvs.Detection.windowTransform, Cvs.Detection.windowTransform, Cvs.Detection.windowTransform]
  have h1 : IntervalIntegrable (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * f s)
      volume 0 L := (Continuous.intervalIntegrable (by fun_prop) 0 L)
  have h2 : IntervalIntegrable (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * g s)
      volume 0 L := (Continuous.intervalIntegrable (by fun_prop) 0 L)
  rw [← intervalIntegral.integral_add h1 h2]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

theorem windowTransform_const_mul (L : ℝ) (c : ℂ) (f : ℝ → ℂ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (fun s => c * f s) ξ = c * Cvs.Detection.windowTransform L f ξ := by
  rw [Cvs.Detection.windowTransform, Cvs.Detection.windowTransform, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

end Cvs.Detection
