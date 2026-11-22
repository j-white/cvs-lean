import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The order-1 half of the endgame: `log M(r)/r² → 0`
-/

noncomputable section

open Filter Topology Asymptotics

namespace Cvs.ZeroFree

/-- `log r / r → 0`. -/
theorem tendsto_log_div_atTop : Tendsto (fun r : ℝ => Real.log r / r) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `1/r² → 0`. -/
theorem tendsto_one_div_sq : Tendsto (fun r : ℝ => 1 / r ^ 2) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hmul : Tendsto (fun r : ℝ => r⁻¹ * r⁻¹) atTop (nhds 0) := by simpa using h.mul h
  refine hmul.congr fun r => ?_
  rw [one_div, ← inv_pow, sq]

/-- `(1 + log 2r)/r → 0` — the shape the growth bound produces after Cauchy. -/
theorem tendsto_one_add_log_two_mul_div :
    Tendsto (fun r : ℝ => (1 + Real.log (2 * r)) / r) atTop (nhds 0) := by
  have h1 : Tendsto (fun r : ℝ => (1 + Real.log 2) * r⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 + Real.log 2)
  have h2 := tendsto_log_div_atTop
  have hsum : Tendsto (fun r : ℝ => (1 + Real.log 2) * r⁻¹ + Real.log r / r) atTop (nhds 0) := by
    simpa using h1.add h2
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.log_mul (by norm_num) (ne_of_gt hr)]
  field_simp
  ring

/-- **The first of's two limits, for an order-1 function.** For `‖ξ(s)‖ ≤ C·exp(A‖s‖(1+log‖s‖))`
the Landau bound on the circle of radius `2r`, run through Cauchy's estimate, tends to zero. -/
theorem tendsto_landau_over_sq {C A : ℝ} (hC : 0 < C) :
    Tendsto (fun r : ℝ =>
      64 * (Real.log (C * Real.exp (A * (2 * r * (1 + Real.log (2 * r))))) + Real.log 2 + 1)
        / r ^ 2) atTop (nhds 0) := by
  have hlim : Tendsto (fun r : ℝ =>
      (64 * (Real.log C + Real.log 2 + 1)) * (1 / r ^ 2)
        + (128 * A) * ((1 + Real.log (2 * r)) / r)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_sq.const_mul (64 * (Real.log C + Real.log 2 + 1))).add
      (tendsto_one_add_log_two_mul_div.const_mul (128 * A))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

end Cvs.ZeroFree
