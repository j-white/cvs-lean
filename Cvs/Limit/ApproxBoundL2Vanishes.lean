import Mathlib

/-!
# The approximation bound drives the L² distance to zero

    ∫ (Ξ ε − ξ)² ≤ (ε + √(ε/δ))²   for every ε > 0   ⟹   the distances tend to `0`

CvS's control on the finite-dimensional eigenvector, read as a convergent sequence.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Limit.ApproxBoundL2Vanishes

/-- **The paper's bound tends to zero.** -/
theorem tendsto_approxBound {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) + Real.sqrt ((1 / ((n : ℝ) + 1)) / δ)) ^ 2)
      atTop (nhds 0) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiv : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / δ) atTop (nhds 0) := by
    have := hε.div_const δ
    simpa using this
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((1 / ((n : ℝ) + 1)) / δ)) atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hdiv
    simpa [Real.sqrt_zero, Function.comp_def] using this
  have hsum : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)
      + Real.sqrt ((1 / ((n : ℝ) + 1)) / δ)) atTop (nhds 0) := by
    have := hε.add hsqrt
    simpa using this
  have := hsum.pow 2
  simpa using this

/-- **The approximants converge in `L²`.** -/
theorem tendsto_of_approx {δ : ℝ} (hδ : 0 < δ) {ξ : ℝ → ℝ} {Ξ : ℝ → ℝ → ℝ}
    (hb : ∀ ε : ℝ, 0 < ε →
      (∫ x : ℝ, (Ξ ε x - ξ x) ^ 2) ≤ (ε + Real.sqrt (ε / δ)) ^ 2) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, (Ξ (1 / ((n : ℝ) + 1)) x - ξ x) ^ 2) atTop (nhds 0) := by
  refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_)
    (tendsto_approxBound hδ)
  exact hb _ (by positivity)

end Cvs.Limit.ApproxBoundL2Vanishes
