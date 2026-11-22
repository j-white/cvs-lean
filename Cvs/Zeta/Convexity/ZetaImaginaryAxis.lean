import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.GammaImaginaryAxis
import Cvs.Zeta.Convexity.ZetaOneLineLog

/-!
# `ζ` on the imaginary axis: `‖ζ(it)‖ ≤ √(|t|/2π)·(7 + log|t|)`

The edge `GammaImaginaryAxis` said was available.
-/

open Complex

namespace Cvs.ZetaGrowth

theorem gammaR_I_ne_zero {t : ℝ} (ht : t ≠ 0) : Gammaℝ ((t : ℂ) * I) ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  have him : ((t : ℂ) * I).im = (-(2 * (n : ℂ))).im := by rw [hn]
  simp at him
  exact ht him

theorem I_ne_zero' {t : ℝ} (ht : t ≠ 0) : ((t : ℂ) * I) ≠ 0 := by
  refine mul_ne_zero ?_ I_ne_zero
  simpa using ht

/-- **The functional equation on the imaginary axis.** -/
theorem zeta_zero_line_eq {t : ℝ} (ht : t ≠ 0) :
    riemannZeta ((t : ℂ) * I)
      = (Gammaℝ (1 - (t : ℂ) * I) / Gammaℝ ((t : ℂ) * I)) * riemannZeta (1 - (t : ℂ) * I) := by
  have hne := gammaR_I_ne_zero ht
  have h1ne : (1 - (t : ℂ) * I) ≠ 0 := by
    intro hc
    have him : (1 - (t : ℂ) * I).im = (0 : ℂ).im := by rw [hc]
    simp at him
    exact ht him
  have hΛ : completedRiemannZeta ((t : ℂ) * I) = Gammaℝ ((t : ℂ) * I) * riemannZeta ((t : ℂ) * I) := by
    rw [riemannZeta_def_of_ne_zero (I_ne_zero' ht)]
    field_simp
  have hΛ' : completedRiemannZeta (1 - (t : ℂ) * I)
      = Gammaℝ (1 - (t : ℂ) * I) * riemannZeta (1 - (t : ℂ) * I) := by
    rw [riemannZeta_def_of_ne_zero h1ne]
    have hg : Gammaℝ (1 - (t : ℂ) * I) ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      have him : (1 - (t : ℂ) * I).im = (-(2 * (n : ℂ))).im := by rw [hn]
      simp at him
      exact ht him
    field_simp
  have hfe : completedRiemannZeta (1 - (t : ℂ) * I) = completedRiemannZeta ((t : ℂ) * I) :=
    completedRiemannZeta_one_sub _
  rw [hΛ, hΛ'] at hfe
  field_simp
  linear_combination -hfe

/-- **`‖ζ(it)‖ ≤ √(|t|/2π)·(7 + log|t|)`.**  The functional equation turns the imaginary axis
into the line `σ = 1`, where `ZetaOneLineLog` applies; `GammaImaginaryAxis` supplies the exact factor. -/
theorem norm_zeta_zero_line {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta ((t : ℂ) * I)‖ ≤ Real.sqrt (|t| / (2 * Real.pi)) * (7 + Real.log |t|) := by
  have ht0 : t ≠ 0 := by
    intro hc; rw [hc] at ht; simp at ht; linarith
  have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  -- reduce to |t|
  have hred : ‖riemannZeta ((t : ℂ) * I)‖ = ‖riemannZeta (((|t| : ℝ) : ℂ) * I)‖ := by
    rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
    · rw [he]
      push_cast
      have hconj : ((t : ℂ) * I) = (starRingEnd ℂ) ((-(t : ℂ)) * I) := by
        apply Complex.ext <;> simp
      rw [hconj, riemannZeta_conj, norm_conj]
  rw [hred]
  set u : ℝ := |t| with hu
  have hu1 : 1 ≤ u := ht
  have hu0 : (0 : ℝ) < u := htabs
  have hune : u ≠ 0 := ne_of_gt hu0
  rw [zeta_zero_line_eq hune, norm_mul, norm_div]
  -- the gamma factor
  have hchi : ‖Gammaℝ (1 - (u : ℂ) * I)‖ / ‖Gammaℝ ((u : ℂ) * I)‖
      ≤ Real.sqrt (u / (2 * Real.pi)) := by
    have hsq := Cvs.ZetaGrowth.norm_chi_sq_le hu0
    have hnn : 0 ≤ ‖Gammaℝ (1 - (u : ℂ) * I)‖ / ‖Gammaℝ ((u : ℂ) * I)‖ := by positivity
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ u / (2 * Real.pi) by positivity),
      Real.sqrt_nonneg (u / (2 * Real.pi)), hsq, hnn]
  -- the zeta factor, via conjugation
  have hzeta : ‖riemannZeta (1 - (u : ℂ) * I)‖ ≤ 7 + Real.log u := by
    have hconj : (1 - (u : ℂ) * I) = (starRingEnd ℂ) (1 + (u : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hconj, riemannZeta_conj, norm_conj]
    have := Cvs.ZetaGrowth.norm_zeta_one_add_I (t := u) (by rw [abs_of_pos hu0]; exact hu1)
    rwa [abs_of_pos hu0] at this
  have hz0 : (0 : ℝ) ≤ 7 + Real.log u := by
    have : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    linarith
  exact mul_le_mul hchi hzeta (norm_nonneg _) (Real.sqrt_nonneg _)

end Cvs.ZetaGrowth
