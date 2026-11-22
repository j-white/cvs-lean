import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts

/-!
# Cubic decay for a doubly-tapered transform
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory
open scoped Real

/-- `‖e^{−isξ}‖ = e^{s·Im ξ}`. -/
theorem norm_char (ξ : ℂ) (s : ℝ) :
    ‖Complex.exp (-((s : ℂ) * ξ) * I)‖ = Real.exp (s * ξ.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The crude modulus bound on the transform: length times sup times the strip's
exponential factor. -/
theorem norm_windowTransform_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ s ∈ Set.uIoc (0 : ℝ) L, ‖f s‖ ≤ M) (ξ : ℂ) :
    ‖Cvs.Detection.windowTransform L f ξ‖ ≤ L * (Real.exp (L * |ξ.im|) * M) := by
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) L,
      ‖Complex.exp (-((s : ℂ) * ξ) * I) * f s‖ ≤ Real.exp (L * |ξ.im|) * M := by
    intro s hs
    rw [Set.uIoc_of_le hL, Set.mem_Ioc] at hs
    rw [norm_mul, norm_char]
    refine mul_le_mul ?_ (hM s (by rw [Set.uIoc_of_le hL, Set.mem_Ioc]; exact hs))
      (norm_nonneg _) (Real.exp_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    calc s * ξ.im ≤ s * |ξ.im| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (le_of_lt hs.1)
      _ ≤ L * |ξ.im| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
  rw [Cvs.Detection.windowTransform]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hL]
  ring

/-- **Integration by parts with the boundary term kept.**  `WindowTransformByParts`'s lemma is the
case `f 0 = f L = 0`. -/
theorem windowTransform_ibp_general {L : ℝ} {f f' : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {ξ : ℂ} (hξ : ξ ≠ 0) :
    Cvs.Detection.windowTransform L f ξ
      = -(1 / (ξ * I)) * (f L * Complex.exp (-((L : ℂ) * ξ) * I) - f 0)
        + (1 / (ξ * I)) * Cvs.Detection.windowTransform L f' ξ := by
  have hu' : IntervalIntegrable f' volume 0 L := hf'.intervalIntegrable 0 L
  have hv' : IntervalIntegrable (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I))
      volume 0 L := (Cvs.Detection.continuous_char ξ).intervalIntegrable 0 L
  have hv : ∀ s ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I) / (-(ξ * I)))
        (Complex.exp (-((s : ℂ) * ξ) * I)) s := fun s _ => Cvs.Detection.hasDerivAt_charAnti hξ s
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hv hu' hv'
  have hcomm : Cvs.Detection.windowTransform L f ξ = ∫ s in (0 : ℝ)..L,
      f s * Complex.exp (-((s : ℂ) * ξ) * I) := by
    rw [Cvs.Detection.windowTransform]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  have hcomm' : Cvs.Detection.windowTransform L f' ξ = ∫ s in (0 : ℝ)..L,
      f' s * Complex.exp (-((s : ℂ) * ξ) * I) := by
    rw [Cvs.Detection.windowTransform]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  have hdiv : ∀ s : ℝ, f' s * (Complex.exp (-((s : ℂ) * ξ) * I) / (-(ξ * I)))
      = (-(1 / (ξ * I))) * (f' s * Complex.exp (-((s : ℂ) * ξ) * I)) := by
    intro s; field_simp
  rw [hcomm, key, intervalIntegral.integral_congr
      (g := fun s => (-(1 / (ξ * I))) * (f' s * Complex.exp (-((s : ℂ) * ξ) * I)))
      fun s _ => hdiv s,
    intervalIntegral.integral_const_mul, ← hcomm']
  norm_num
  field_simp
  rw [Complex.I_sq]
  ring

end Cvs.Detection
