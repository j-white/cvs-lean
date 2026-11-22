import Mathlib

/-!
# Cauchy–Schwarz for integrals on the line

    |∫ f·g| ≤ √(∫ f²) · √(∫ g²)

stated in the raw integrals `Cvs.WeilForm.SelfConvolutionFunctional`'s Weil form is written in, so no channel has to be
restated in `Lp` to use it.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory

namespace Cvs.Upstream.CauchySchwarzLine

/-- **The norm of a real class, as an integral.** -/
theorem norm_toLp_sq_real {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  have hinner : (inner (𝕜 := ℝ) (hf.toLp f) (hf.toLp f) : ℝ) = ∫ x : ℝ, f x ^ 2 := by
    rw [L2.inner_def]
    refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
    simp [hx, sq]
  rw [← hinner, real_inner_self_eq_norm_sq]

/-- **Cauchy–Schwarz.** -/
theorem abs_integral_mul_le {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    |∫ x : ℝ, f x * g x| ≤ Real.sqrt (∫ x : ℝ, f x ^ 2) * Real.sqrt (∫ x : ℝ, g x ^ 2) := by
  have hinner : (inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g) : ℝ) = ∫ x : ℝ, f x * g x := by
    rw [L2.inner_def]
    refine integral_congr_ae ((hf.coeFn_toLp.and hg.coeFn_toLp).mono fun x hx => ?_)
    simp [hx.1, hx.2, mul_comm]
  have hcs : |(inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g) : ℝ)| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ :=
    abs_real_inner_le_norm _ _
  rw [hinner] at hcs
  rwa [← Real.sqrt_sq (norm_nonneg (hf.toLp f)), ← Real.sqrt_sq (norm_nonneg (hg.toLp g)),
    norm_toLp_sq_real hf, norm_toLp_sq_real hg] at hcs

end Cvs.Upstream.CauchySchwarzLine
