import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.PoleChannelWindowL2
import Cvs.WeilForm.PrimeChannelL2Continuous
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.UnitWindowTransformBounded
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Lévy energy is bounded on the form's sublevel set

    archFull f ≤ B + 2·Wp·Wn + |archSymbol 0| + 2·primeMass

for a unit window function with `weilForm f ≤ B`: the other three channels are bounded by the
norm alone, so whatever the form does not spend on them is a cap on the archimedean part.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.LevyEnergySublevelBound

/-- The pole channel is bounded by the norm. -/
theorem abs_poleTerm_le {L : ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (hnorm : (∫ x : ℝ, f x ^ 2) = 1) :
    |2 * (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))|
      ≤ 2 * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
          * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2) := by
  have hwp := Cvs.WeilForm.PoleChannelWindowL2.memLp_poleWeightPos (L := L)
  have hwn := Cvs.WeilForm.PoleChannelWindowL2.memLp_poleWeightNeg (L := L)
  rw [Cvs.WeilForm.PoleChannelWindowL2.integral_eq_window hsupp (fun s : ℝ => Real.exp (s / 2)),
    Cvs.WeilForm.PoleChannelWindowL2.integral_eq_window hsupp (fun s : ℝ => Real.exp (-(s / 2))),
    show Set.indicator (Set.Ioc (0:ℝ) L) (fun s : ℝ => Real.exp (s / 2))
      = Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L from rfl,
    show Set.indicator (Set.Ioc (0:ℝ) L) (fun s : ℝ => Real.exp (-(s / 2)))
      = Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L from rfl]
  have h1 := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hwp
  have h2 := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hwn
  rw [hnorm, Real.sqrt_one, one_mul] at h1 h2
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hmul : |∫ s : ℝ, f s * Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L s|
      * |∫ s : ℝ, f s * Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L s|
      ≤ Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
        * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2) :=
    mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hmul]

/-- The prime channel is bounded by the norm. -/
theorem abs_primeSide_le (P R : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hnorm : (∫ x : ℝ, f x ^ 2) = 1) :
    |primePowerSideTruncated P R (selfConvolution f)|
      ≤ 2 * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R := by
  classical
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      |(ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
        * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k)))|
        ≤ |ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ)| * 2 := by
    intro k _
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hb1 := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le (f := f) (Real.log k) hf
    have hb2 := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le (f := f) (-(Real.log k)) hf
    rw [hnorm] at hb1 hb2
    calc |selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k))|
        ≤ |selfConvolution f (Real.log k)| + |selfConvolution f (-(Real.log k))| :=
          abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add hb1 hb2
      _ = 2 := by norm_num
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, Cvs.WeilForm.PrimeChannelL2Continuous.primeMass]
  ring_nf
  rfl

/-- **The archimedean energy is capped by the form.** -/
theorem archFull_le {L : ℝ} (P R : ℕ) {f : ℝ → ℝ} {B : ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hnorm : (∫ x : ℝ, f x ^ 2) = 1)
    (hform : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f ≤ B) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
      ≤ B + 2 * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
            * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2)
          + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 2 * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R := by
  have hzero : selfConvolution f 0 = 1 := by
    rw [Cvs.WeilForm.UnitWindowTransformBounded.selfConvolution_zero, hnorm]
  have hpole := abs_poleTerm_le hf hsupp hnorm
  have hprime := abs_primeSide_le P R hf hnorm
  have hform' := hform
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq] at hform'
  rw [hzero] at hform'
  have hA := abs_le.mp hpole
  have hC := abs_le.mp hprime
  have hS := abs_le.mp (le_refl |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0|)
  have hSle : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≥ -|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| :=
    neg_abs_le _
  have harch : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution f 0 - selfConvolution f (u / 2)) := rfl
  rw [harch, hzero] at *
  linarith [hA.1, hA.2, hC.1, hC.2, hSle]

end Cvs.WeilForm.LevyEnergySublevelBound
