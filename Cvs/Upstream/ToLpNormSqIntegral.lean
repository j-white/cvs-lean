import Mathlib

/-!
# The norm of an L² class is the integral of the squared norm

    ‖MemLp.toLp f‖² = ∫ ‖f x‖² dx

Read right to left this turns an integral bound between two functions into a distance bound
between their classes, where completeness of `Lp` is available.
-/

noncomputable section

open MeasureTheory

namespace Cvs.Upstream.ToLpNormSqIntegral

/-- **The norm of a class, as an integral.** -/
theorem norm_toLp_sq {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hinner : (inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f) : ℂ)
      = ((∫ x : ℝ, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
    simp only [hx]
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    exact rfl
  have hre := congrArg Complex.re hinner
  simpa [inner_self_eq_norm_sq, ← Complex.ofReal_pow] using hre

/-- **An integral bound between two functions is a distance bound between their classes.** -/
theorem dist_toLp_le {f g : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) {ε : ℝ}
    (h : (∫ x : ℝ, ‖f x - g x‖ ^ 2) ≤ ε) :
    dist (hf.toLp f) (hg.toLp g) ≤ Real.sqrt ε := by
  have hsub : (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g := MemLp.toLp_sub hf hg
  have hnorm : ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x : ℝ, ‖f x - g x‖ ^ 2 := by
    rw [← hsub, norm_toLp_sq (hf.sub hg)]
    rfl
  have hle : ‖hf.toLp f - hg.toLp g‖ ^ 2 ≤ ε := by rw [hnorm]; exact h
  calc dist (hf.toLp f) (hg.toLp g)
      = ‖hf.toLp f - hg.toLp g‖ := dist_eq_norm _ _
    _ = Real.sqrt (‖hf.toLp f - hg.toLp g‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hle

end Cvs.Upstream.ToLpNormSqIntegral
