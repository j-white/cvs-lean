import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial bounds for `arctan`, and the constants a channel certificate needs

    `z − z³/3 + z⁵/5 − z⁷/7 ≤ arctan z ≤ z − z³/3 + z⁵/5`   for `z ≥ 0`

with the reductions `arctan z = π/4 + arctan((z−1)/(z+1))` and `arctan z = π/2 − arctan(1/z)`,
and rational bounds on `π/4`, `π/2` and `log 2 / 2`.
-/

noncomputable section

open Real Set

namespace Cvs.Upstream.ArctanPolynomialBounds

/-- **The degree-seven Taylor polynomial is a lower bound**: the difference has derivative
`x⁸/(1+x²) ≥ 0` and vanishes at `0`. -/
theorem arctan_ge_poly7 {z : ℝ} (hz : 0 ≤ z) : z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 ≤ arctan z := by
  let f : ℝ → ℝ := fun x => arctan x - (x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7)
  have hderiv : ∀ x : ℝ, HasDerivAt f (1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7)
        (1 - x ^ 2 + x ^ 4 - x ^ 6) x := by
      have := (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
        ((hasDerivAt_pow 5 x).div_const 5)).sub ((hasDerivAt_pow 7 x).div_const 7)
      exact this.congr_deriv (by push_cast; ring)
    exact (hasDerivAt_arctan x).sub h2
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hderiv x).deriv]
    have : 1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6) = x ^ 8 / (1 + x ^ 2) := by
      field_simp; ring
    rw [this]; positivity
  have h := hmono (Set.mem_Ici.mpr le_rfl) hz hz
  simp only [f, arctan_zero] at h
  linarith

/-- **The degree-five Taylor polynomial is an upper bound**: the difference has derivative
`x⁶/(1+x²) ≥ 0` and vanishes at `0`. -/
theorem arctan_le_poly5 {z : ℝ} (hz : 0 ≤ z) : arctan z ≤ z - z ^ 3 / 3 + z ^ 5 / 5 := by
  let f : ℝ → ℝ := fun x => (x - x ^ 3 / 3 + x ^ 5 / 5) - arctan x
  have hderiv : ∀ x : ℝ, HasDerivAt f ((1 - x ^ 2 + x ^ 4) - 1 / (1 + x ^ 2)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x - x ^ 3 / 3 + x ^ 5 / 5) (1 - x ^ 2 + x ^ 4) x := by
      have := ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
        ((hasDerivAt_pow 5 x).div_const 5)
      exact this.congr_deriv (by push_cast; ring)
    exact h2.sub (hasDerivAt_arctan x)
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hderiv x).deriv]
    have : (1 - x ^ 2 + x ^ 4) - 1 / (1 + x ^ 2) = x ^ 6 / (1 + x ^ 2) := by
      field_simp; ring
    rw [this]; positivity
  have h := hmono (Set.mem_Ici.mpr le_rfl) hz hz
  simp only [f, arctan_zero] at h
  linarith

/-- **Reduction to the unit interval** through `π/4`. -/
theorem arctan_eq_add_pi4 {z : ℝ} (hz : -1 < z) :
    arctan z = π / 4 + arctan ((z - 1) / (z + 1)) := by
  have h := arctan_add (x := z) (y := -1) (by linarith)
  rw [arctan_neg, arctan_one] at h
  have : (z + -1) / (1 - z * -1) = (z - 1) / (z + 1) := by ring_nf
  rw [this] at h
  linarith

/-- **Reduction to the unit interval** through `π/2`. -/
theorem arctan_eq_pi2_sub {z : ℝ} (hz : 0 < z) : arctan z = π / 2 - arctan (1 / z) := by
  rw [one_div, arctan_inv_of_pos hz]; ring

theorem pi_div_four_gt : (78539816 : ℝ) / 100000000 < π / 4 := by
  have := pi_gt_d20; linarith
theorem pi_div_two_gt8 : (157079632 : ℝ) / 100000000 < π / 2 := by
  have := pi_gt_d20; linarith
theorem pi_div_two_gt6 : (1570796 : ℝ) / 1000000 < π / 2 := by
  have := pi_gt_d20; linarith
theorem half_log_two_lt : Real.log 2 / 2 < (3465735904 : ℝ) / 10000000000 := by
  have := log_two_lt_d9; linarith

end Cvs.Upstream.ArctanPolynomialBounds
