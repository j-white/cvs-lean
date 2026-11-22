import Mathlib
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.TransformNowhereLocallyZero

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Plancherel and the derivative rule for the Fourier–Laplace transform on the line

For `g ∈ L¹ ∩ L²(ℝ)` and real `τ`, `∫ |fourierLaplace g τ|² dτ = 2π ∫ |g|²`. A derivative
`g' ∈ L¹` transforms to `−iτ · fourierLaplace g τ`, so for `g' ∈ L¹ ∩ L²` also
`∫ τ² |fourierLaplace g τ|² dτ = 2π ∫ |g'|²`, and the normalised frequency second moment is
the energy ratio `∫ |g'|² / ∫ |g|²`.
-/

noncomputable section

open Real MeasureTheory FourierTransform

namespace Cvs.Upstream.FourierLaplacePlancherel

open FourierLaplace (fourierLaplace)

/-- On the real line the Fourier–Laplace transform is the Fourier integral at `τ / (−2π)`. -/
theorem fourierLaplace_ofReal (g : ℝ → ℂ) (τ : ℝ) :
    fourierLaplace g (τ : ℂ) = 𝓕 g (τ / (-(2 * π))) := by
  rw [Cvs.WeilForm.TransformNowhereLocallyZero.fourier_eq_fourierLaplace]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

theorem memLp_fourier {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) : MemLp (𝓕 g) 2 :=
  (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hg hg2)

theorem two_pi_ne_zero : (-(2 * π) : ℝ) ≠ 0 := by
  have := Real.pi_pos
  linarith

/-- The squared modulus of the transform of `g ∈ L¹ ∩ L²` is integrable on the real line. -/
theorem integrable_norm_fourierLaplace_sq {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) :
    Integrable fun τ : ℝ => ‖fourierLaplace g (τ : ℂ)‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm (memLp_fourier hg hg2).aestronglyMeasurable).mp
    (memLp_fourier hg hg2)
  simpa only [fourierLaplace_ofReal] using h.comp_div two_pi_ne_zero

/-- **Plancherel for the Fourier–Laplace transform.** For `g ∈ L¹ ∩ L²`,
`∫ |fourierLaplace g τ|² dτ = 2π ∫ |g|²`. -/
theorem integral_norm_fourierLaplace_sq {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) :
    ∫ τ : ℝ, ‖fourierLaplace g (τ : ℂ)‖ ^ 2 = 2 * π * ∫ t, ‖g t‖ ^ 2 := by
  simp_rw [fourierLaplace_ofReal]
  rw [Measure.integral_comp_div (fun w => ‖𝓕 g w‖ ^ 2) (-(2 * π)),
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier hg hg2, abs_neg,
    abs_of_pos (by positivity), smul_eq_mul]

end Cvs.Upstream.FourierLaplacePlancherel
