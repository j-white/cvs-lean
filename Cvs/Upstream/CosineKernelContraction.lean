import Mathlib
import Cvs.Upstream.PlancherelTimeLimited
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.WindowSpectralDensityBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine-kernel operator is a contraction from `L²(E)` to `L²(S)`

For `c > 0`, `f ∈ L¹ ∩ L²(ℝ)` and any set `S`, `∫_S (√(c/2π) ∫ cos(cst) f(t) dt)² ds ≤ ∫ f²`: the inner
integral is the real part of `𝓕 f (cs/2π)` and Plancherel (Cvs.Upstream.PlancherelTimeLimited) gives `∫ ‖𝓕 f‖² = ∫ f²`.
Applied to `1_E G`: `∫_S (kerOp (cosKer c) E G)² ≤ ∫_E G²`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped FourierTransform

namespace Cvs.Upstream.CosineKernelContraction


/-- **The cosine integral is dominated by the transform**:
`(√(c/2π) ∫ cos(cst) f(t) dt)² ≤ (c/2π) ‖𝓕 f ((c/2π) s)‖²` for `c ≥ 0` and `f` integrable. -/
theorem sq_cosIntegral_le {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    (√(c / (2 * π)) * ∫ t, Real.cos (c * s * t) * f t) ^ 2
      ≤ c / (2 * π) * ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (c / (2 * π) * s)‖ ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity), Cvs.WeilForm.WindowSpectralDensityBound.norm_fourier_sq_eq hf]
  have e : ∫ t, Real.cos (c * s * t) * f t = ∫ v, f v * Real.cos (2 * π * v * (c / (2 * π) * s)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have : 2 * π * v * (c / (2 * π) * s) = c * s * v := by field_simp
    simp only [this]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)

/-- **The cosine transform is a contraction** (Plancherel): for `c > 0`, `f ∈ L¹ ∩ L²(ℝ)` and any set `S`,
`∫_S (√(c/2π) ∫ cos(cst) f(t) dt)² ds ≤ ∫ f²`. -/
theorem setIntegral_sq_cosIntegral_le {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hf1 : Integrable f) (S : Set ℝ) :
    ∫ s in S, (√(c / (2 * π)) * ∫ t, Real.cos (c * s * t) * f t) ^ 2 ≤ ∫ t, f t ^ 2 := by
  set a : ℝ := c / (2 * π) with ha
  have ha0 : 0 < a := by positivity
  set F : ℝ → ℝ := fun ξ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 with hF
  have hFi : Integrable F := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf2 hf1
  have hBi : Integrable fun s => a * F (a * s) := (hFi.comp_mul_left' ha0.ne').const_mul a
  have hB0 : ∀ s, 0 ≤ a * F (a * s) := fun s => by positivity
  calc ∫ s in S, (√a * ∫ t, Real.cos (c * s * t) * f t) ^ 2
      ≤ ∫ s in S, a * F (a * s) :=
        integral_mono_of_nonneg (ae_of_all _ fun s => sq_nonneg _) hBi.integrableOn
          (ae_of_all _ fun s => sq_cosIntegral_le hc.le hf1 s)
    _ ≤ ∫ s, a * F (a * s) := setIntegral_le_integral hBi (ae_of_all _ hB0)
    _ = ∫ ξ, F ξ := by
        rw [integral_const_mul, Measure.integral_comp_mul_left (fun ξ => F ξ) a, smul_eq_mul,
          abs_of_pos (inv_pos.2 ha0), ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
    _ = ∫ t, f t ^ 2 := Cvs.Upstream.PlancherelTimeLimited.plancherel_of_integrable hf2 hf1

end Cvs.Upstream.CosineKernelContraction
