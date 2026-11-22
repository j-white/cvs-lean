import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# Integration by parts for the window transform

`HannWindowShifts` gave the algebraic identity behind the Hann taper.
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory
open scoped Real

/-- The character's derivative in the real variable. -/
theorem hasDerivAt_char (ξ : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I))
      (Complex.exp (-((s : ℂ) * ξ) * I) * (-(ξ * I))) s := by
  have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(ξ * I))) (-(ξ * I)) s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(ξ * I))
  have hfun : (fun t : ℝ => (t : ℂ) * (-(ξ * I))) = fun t : ℝ => -((t : ℂ) * ξ) * I := by
    funext t; ring
  rw [hfun] at hlin
  exact hlin.cexp

theorem char_ne_zero_factor {ξ : ℂ} (hξ : ξ ≠ 0) : -(ξ * I) ≠ 0 := by
  simp [hξ, Complex.I_ne_zero]

/-- The antiderivative of the character. -/
theorem hasDerivAt_charAnti {ξ : ℂ} (hξ : ξ ≠ 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I) / (-(ξ * I)))
      (Complex.exp (-((s : ℂ) * ξ) * I)) s := by
  have h := (hasDerivAt_char ξ s).div_const (-(ξ * I))
  rwa [mul_div_assoc, div_self (char_ne_zero_factor hξ), mul_one] at h

theorem continuous_char (ξ : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I)) := by fun_prop

/-- **One integration by parts.**  The boundary term is exactly what a taper
kills; with `f` vanishing at both ends it drops and one power of `ξ` is gained. -/
theorem windowTransform_ibp {L : ℝ} {f f' : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (f' s) s)
    (hf' : Continuous f') (h0 : f 0 = 0) (hLz : f L = 0) {ξ : ℂ} (hξ : ξ ≠ 0) :
    Cvs.Detection.windowTransform L f ξ = (1 / (ξ * I)) * Cvs.Detection.windowTransform L f' ξ := by
  have hu' : IntervalIntegrable f' volume 0 L := hf'.intervalIntegrable 0 L
  have hv' : IntervalIntegrable (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I))
      volume 0 L := (continuous_char ξ).intervalIntegrable 0 L
  have hv : ∀ s ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I) / (-(ξ * I)))
        (Complex.exp (-((s : ℂ) * ξ) * I)) s := fun s _ => hasDerivAt_charAnti hξ s
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hv hu' hv'
  rw [h0, hLz] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  -- windowTransform puts the character on the left; multiplication commutes
  have hcomm : Cvs.Detection.windowTransform L f ξ = ∫ s in (0 : ℝ)..L,
      f s * Complex.exp (-((s : ℂ) * ξ) * I) := by
    rw [Cvs.Detection.windowTransform]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  have hcomm' : Cvs.Detection.windowTransform L f' ξ = ∫ s in (0 : ℝ)..L,
      f' s * Complex.exp (-((s : ℂ) * ξ) * I) := by
    rw [Cvs.Detection.windowTransform]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  rw [hcomm, key, hcomm']
  have hdiv : ∀ s : ℝ, f' s * (Complex.exp (-((s : ℂ) * ξ) * I) / (-(ξ * I)))
      = (-(1 / (ξ * I))) * (f' s * Complex.exp (-((s : ℂ) * ξ) * I)) := by
    intro s
    field_simp
  rw [intervalIntegral.integral_congr (g := fun s => (-(1 / (ξ * I)))
      * (f' s * Complex.exp (-((s : ℂ) * ξ) * I))) fun s _ => hdiv s,
    intervalIntegral.integral_const_mul]
  ring

/-- **Two integrations by parts.**  Needs the taper's derivative to vanish at the
ends as well; the Hann window supplies exactly this and no more. -/
theorem windowTransform_ibp_two {L : ℝ} {f f' f'' : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (f' s) s)
    (hg : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f' (f'' s) s)
    (hf' : Continuous f') (hf'' : Continuous f'')
    (h0 : f 0 = 0) (hLz : f L = 0) (h0' : f' 0 = 0) (hLz' : f' L = 0)
    {ξ : ℂ} (hξ : ξ ≠ 0) :
    Cvs.Detection.windowTransform L f ξ
      = (1 / (ξ * I)) * ((1 / (ξ * I)) * Cvs.Detection.windowTransform L f'' ξ) := by
  rw [windowTransform_ibp hf hf' h0 hLz hξ, windowTransform_ibp hg hf'' h0' hLz' hξ]

end Cvs.Detection
