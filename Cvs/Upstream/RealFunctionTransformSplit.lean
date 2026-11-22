import Mathlib

/-!
# The transform of a real function

A real function's transform splits into its cosine and sine pairings, and its squared modulus is
the sum of their squares.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology
open scoped FourierTransform

namespace Cvs.Upstream.RealFunctionTransformSplit

variable {f : ℝ → ℝ}

/-- The cosine pairing at frequency `w`. -/
def cosPart (f : ℝ → ℝ) (w : ℝ) : ℝ := ∫ x : ℝ, f x * Real.cos (2 * Real.pi * w * x)

/-- The sine pairing at frequency `w`. -/
def sinPart (f : ℝ → ℝ) (w : ℝ) : ℝ := ∫ x : ℝ, f x * Real.sin (2 * Real.pi * w * x)

theorem integrable_mul_trig (hf : Integrable f) {g : ℝ → ℝ} (hg : Continuous g)
    (hbd : ∀ x, |g x| ≤ 1) (c : ℝ) :
    Integrable fun x : ℝ => f x * g (c * x) := by
  refine hf.abs.mono' (hf.aestronglyMeasurable.mul (hg.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [hbd (c * x), abs_nonneg (f x), abs_nonneg (g (c * x))]

/-- **A real function's transform splits.** -/
theorem fourier_real_split (hf : Integrable f) (w : ℝ) :
    𝓕 (fun x : ℝ => (f x : ℂ)) w = ((cosPart f w : ℝ) : ℂ) - Complex.I * ((sinPart f w : ℝ) : ℂ) := by
  have hIc := integrable_mul_trig hf Real.continuous_cos Real.abs_cos_le_one (2 * Real.pi * w)
  have hIs := integrable_mul_trig hf Real.continuous_sin Real.abs_sin_le_one (2 * Real.pi * w)
  rw [Real.fourier_real_eq_integral_exp_smul]
  have key : ∀ v : ℝ, Complex.exp ((↑(-2 * Real.pi * v * w) : ℂ) * Complex.I) • ((f v : ℝ) : ℂ)
      = ((f v * Real.cos (2 * Real.pi * w * v) : ℝ) : ℂ)
        - Complex.I * ((f v * Real.sin (2 * Real.pi * w * v) : ℝ) : ℂ) := by
    intro v
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (-2 * Real.pi * v * w : ℝ) = -(2 * Real.pi * w * v) from by ring,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  have h1 : Integrable fun v : ℝ => ((f v * Real.cos (2 * Real.pi * w * v) : ℝ) : ℂ) := hIc.ofReal
  have h2 : Integrable fun v : ℝ =>
      Complex.I * ((f v * Real.sin (2 * Real.pi * w * v) : ℝ) : ℂ) := (hIs.ofReal).const_mul _
  have hre : ∀ g : ℝ → ℝ, Integrable g → (∫ x : ℝ, ((g x : ℝ) : ℂ)) = ((∫ x : ℝ, g x : ℝ) : ℂ) :=
    fun g hg => by simpa using Complex.ofRealCLM.integral_comp_comm hg
  rw [integral_sub h1 h2, integral_const_mul, hre _ hIc, hre _ hIs, cosPart, sinPart]

end Cvs.Upstream.RealFunctionTransformSplit
