import Mathlib
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The prime channel is L²-continuous

    |primeSide f − primeSide h| ≤ 2·‖f−h‖₂(‖f‖₂+‖h‖₂)·∑ |weights|

The truncated prime side is a finite sum of self-convolution values, and `Cvs.WeilForm.SelfConvolutionL2Continuous` bounds each
of them by the same quantity.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeChannelL2Continuous

/-- The total mass of the truncated prime weights. -/
def primeMass (P R : ℕ) : ℝ :=
  ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
    |ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ)|

/-- **The prime channel is `L²`-continuous.** -/
theorem abs_primeSide_sub_le (P R : ℕ) {f h : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ)) :
    |primePowerSideTruncated P R (selfConvolution f)
        - primePowerSideTruncated P R (selfConvolution h)|
      ≤ 2 * (Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
            * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)))
          * primeMass P R := by
  classical
  set K : ℝ := Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
      * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image,
    Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      |(ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k)))
        - (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution h (Real.log k) + selfConvolution h (-(Real.log k)))|
        ≤ |ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ)| * (2 * K) := by
    intro k _
    have hb1 := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := f) (h := h)
      (Real.log k) hf hh
    have hb2 := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := f) (h := h)
      (-(Real.log k)) hf hh
    have hfac : (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
        * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k)))
      - (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
        * (selfConvolution h (Real.log k) + selfConvolution h (-(Real.log k)))
      = (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
        * ((selfConvolution f (Real.log k) - selfConvolution h (Real.log k))
          + (selfConvolution f (-(Real.log k)) - selfConvolution h (-(Real.log k)))) := by
      ring
    rw [hfac, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |(selfConvolution f (Real.log k) - selfConvolution h (Real.log k))
            + (selfConvolution f (-(Real.log k)) - selfConvolution h (-(Real.log k)))|
        ≤ |selfConvolution f (Real.log k) - selfConvolution h (Real.log k)|
            + |selfConvolution f (-(Real.log k)) - selfConvolution h (-(Real.log k))| :=
          abs_add_le _ _
      _ ≤ K + K := add_le_add hb1 hb2
      _ = 2 * K := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, primeMass]
  ring_nf
  rfl

end Cvs.WeilForm.PrimeChannelL2Continuous
