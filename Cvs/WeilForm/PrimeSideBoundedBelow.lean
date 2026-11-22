import Mathlib
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The prime side is a bounded perturbation, and the window form is bounded below

    |prime side| ≤ 2·W·g 0,    W = ∑_k Λ(k)·k^{−1/2} over the truncation's prime powers

by `Cvs.WeilForm.SelfConvolutionMaximum`'s `|g u| ≤ g 0`, so `Cvs.WeilForm.SelfConvolutionFunctional`'s form is bounded below by its pole term plus
`(archSymbol 0 − 2W)·g 0`: the whole prime side costs at most a multiple of the norm.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeSideBoundedBelow

/-- The total prime weight the truncation carries. -/
def primeWeightTotal (P R : ℕ) : ℝ :=
  ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
    ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ)

/-- Each weight is nonnegative. -/
theorem weight_nonneg (k : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ) :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)

theorem primeWeightTotal_nonneg (P R : ℕ) : 0 ≤ primeWeightTotal P R :=
  Finset.sum_nonneg fun k _ => weight_nonneg k

/-- **The prime side costs at most a multiple of the norm.**  Every prime power sees the
self-convolution at a shift, and `Cvs.WeilForm.SelfConvolutionMaximum` caps each of those by its value at the origin. -/
theorem abs_primePowerSideTruncated_le (P R : ℕ) {f : ℝ → ℝ}
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u)) :
    |primePowerSideTruncated P R (selfConvolution f)|
      ≤ 2 * primeWeightTotal P R * selfConvolution f 0 := by
  classical
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      |(ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k)))|
        ≤ (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
            * (2 * selfConvolution f 0) := by
    intro k _
    rw [abs_mul, abs_of_nonneg (weight_nonneg k)]
    refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg k)
    refine le_trans (abs_add_le _ _) ?_
    have h1 := Cvs.WeilForm.SelfConvolutionMaximum.abs_selfConvolution_le (f := f) (Real.log k) hsq
      (hcross (Real.log k))
    have h2 := Cvs.WeilForm.SelfConvolutionMaximum.abs_selfConvolution_le (f := f) (-(Real.log k)) hsq
      (hcross (-(Real.log k)))
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, primeWeightTotal]
  exact le_of_eq (by ring)

end Cvs.WeilForm.PrimeSideBoundedBelow
