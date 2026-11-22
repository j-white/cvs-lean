import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# One bound across `σ = 1`, and Cauchy's estimate for `ζ'`

The mean-value step needs `‖ζ'‖`, and Cauchy's estimate gets it from `‖ζ‖` on a circle.
-/

noncomputable section

open Complex Metric

namespace Cvs.ZeroFree

/-- `ζ` is differentiable on a closed ball avoiding its pole. -/
theorem diffContOnCl_zeta {s : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ closedBall s R) :
    DiffContOnCl ℂ riemannZeta (ball s R) := by
  constructor
  · intro w hw
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro hc
    exact h1 (by rw [← hc]; exact ball_subset_closedBall hw)
  · intro w hw
    rw [closure_ball s (ne_of_gt hR)] at hw
    refine (differentiableAt_riemannZeta ?_).continuousAt.continuousWithinAt
    intro hc
    exact h1 (by rw [← hc]; exact hw)

/-- **Cauchy's estimate for `ζ'`.**  `‖ζ'(s)‖ ≤ M/R` from a bound `M` on the circle. -/
theorem norm_deriv_zeta_le {s : ℂ} {R M : ℝ} (hR : 0 < R)
    (hpole : (1 : ℂ) ∉ closedBall s R)
    (hM : ∀ w ∈ sphere s R, ‖riemannZeta w‖ ≤ M) :
    ‖deriv riemannZeta s‖ ≤ M / R :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR (diffContOnCl_zeta hR hpole) hM

end Cvs.ZeroFree
