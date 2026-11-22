import Mathlib
import Cvs.Finite.ExponentialKernelLocalises

/-!
# The kernel on an exponential

`Kb` applied to `e^{νs}` returns `2b/(b²−ν²)·e^{νs}` plus two boundary exponentials, so the
symbol coefficient is what survives away from the window's ends.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Finite.ExponentialKernelLocalises

namespace Cvs.Finite.ExponentialKernelValue

/-- `∫ₐᵇ e^{cu} du` for `c ≠ 0`. -/
theorem integral_exp_mul {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (∫ u in a..b, Real.exp (c * u)) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u : ℝ => Real.exp (c * u) / c) (Real.exp (c * x)) x := by
    intro x
    have h := (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_expMul c x).div_const c
    refine h.congr_deriv ?_
    field_simp
  have hcont : Continuous fun u : ℝ => Real.exp (c * u) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hcont.intervalIntegrable _ _)]
  ring

end Cvs.Finite.ExponentialKernelValue
