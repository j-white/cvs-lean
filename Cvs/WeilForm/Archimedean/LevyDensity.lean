import Mathlib

/-!
# Summing the Lévy terms into one density

    ∑ₖ e^{−(¼+k)u} = e^{−u/4}/(1 − e^{−u}),     u > 0

and that density, pushed through `u = 2v`, is exactly `Levy.rho`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace Cvs.WeilForm.Archimedean.LevyDensity

/-- The Lévy density in the variable the digamma series produces. -/
def densityU (u : ℝ) : ℝ := Real.exp (-(u / 4)) / (1 - Real.exp (-u))

/-- **The geometric sum over the shifted poles.** -/
theorem hasSum_exp (u : ℝ) (hu : 0 < u) :
    HasSum (fun k : ℕ => Real.exp (-((1 / 4 + (k : ℝ)) * u))) (densityU u) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun k : ℕ => (Real.exp (-u)) ^ k) (1 - Real.exp (-u))⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  have hcongr : ∀ k : ℕ, Real.exp (-(u / 4)) * (Real.exp (-u)) ^ k
      = Real.exp (-((1 / 4 + (k : ℝ)) * u)) := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have := hgeom.mul_left (Real.exp (-(u / 4)))
  rw [funext hcongr] at this
  rwa [densityU, div_eq_mul_inv]

/-- **The density is positive.** -/
theorem densityU_pos {u : ℝ} (hu : 0 < u) : 0 < densityU u := by
  have h1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold densityU
  have : (0:ℝ) < 1 - Real.exp (-u) := by linarith
  positivity

end Cvs.WeilForm.Archimedean.LevyDensity
