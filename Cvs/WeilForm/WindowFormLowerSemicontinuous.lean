import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.PoleChannelWindowL2
import Cvs.WeilForm.PrimeChannelL2Continuous
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form is lower semicontinuous along L² convergence

    weilForm f − ε ≤ weilForm (F n)   eventually

Pole and prime channels are continuous, the archimedean channel is lower semicontinuous, and
a sum of the two is lower semicontinuous.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowFormLowerSemicontinuous

/-- **Lower semicontinuity of the window's Weil form.** -/
theorem weilForm_le_eventually {L C ε : ℝ} (P R : ℕ) {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hfs : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hFs : ∀ n, ∀ s ∉ Set.Ioc (0:ℝ) L, F n s = 0)
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hFc : ∀ n, AEStronglyMeasurable (selfConvolution (F n)) (volume : Measure ℝ))
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ))
    (hFint : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (F n)) (Set.Ioi 0)
      (volume : Measure ℝ))
    (hconv : Tendsto (fun n => ∫ x : ℝ, (F n x - f x) ^ 2) atTop (nhds 0))
    (hbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ C) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f - ε
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ, (F n x - f x) ^ 2) with hs
  set Ef : ℝ := Real.sqrt (∫ x : ℝ, f x ^ 2) with hEf
  set Bc : ℝ := Real.sqrt C + Ef with hBc
  set Wp : ℝ := Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2) with hWp
  set Wn : ℝ := Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2) with hWn
  set a : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 with ha
  set M : ℝ := 2 * Wp * Wn * Bc + |a| * Bc
      + 2 * Bc * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R with hM
  have hsnn : ∀ n, 0 ≤ s n := fun n => Real.sqrt_nonneg _
  have hEfnn : 0 ≤ Ef := Real.sqrt_nonneg _
  have hWpnn : 0 ≤ Wp := Real.sqrt_nonneg _
  have hWnnn : 0 ≤ Wn := Real.sqrt_nonneg _
  have hmassnn : 0 ≤ Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hBcnn : 0 ≤ Bc := by rw [hBc]; positivity
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hstend : Tendsto s atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [hs, Real.sqrt_zero, Function.comp_def] using this
  have hev : ∀ᶠ n in atTop, s n * M < ε / 2 :=
    (by simpa using hstend.mul_const M : Tendsto (fun n => s n * M) atTop (nhds 0)).eventually_lt_const
      (by linarith : (0:ℝ) < ε / 2)
  have harch := Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.archFull_le_eventually hf hfc hint hF hFc hFint hconv hbdd
    (by linarith : (0:ℝ) < ε / 2)
  filter_upwards [hev, harch] with n hn harchn
  have hEn : Real.sqrt (∫ x : ℝ, F n x ^ 2) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbdd n)
  have hKle : s n * (Real.sqrt (∫ x : ℝ, F n x ^ 2) + Ef) ≤ s n * Bc := by
    refine mul_le_mul_of_nonneg_left ?_ (hsnn n)
    rw [hBc]; linarith
  -- pole channel
  have hpole := Cvs.WeilForm.PoleChannelWindowL2.abs_poleTerm_sub_le (hF n) hf (hFs n) hfs
  have hpole' : |2 * (∫ x : ℝ, F n x * Real.exp (x / 2)) * (∫ x : ℝ, F n x * Real.exp (-(x / 2)))
      - 2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))|
      ≤ s n * (2 * Wp * Wn * Bc) := by
    refine le_trans hpole ?_
    have : 2 * s n * Wp * Wn * (Real.sqrt (∫ x : ℝ, F n x ^ 2) + Ef)
        ≤ 2 * s n * Wp * Wn * Bc := by
      refine mul_le_mul_of_nonneg_left (by rw [hBc]; linarith) (by positivity)
    nlinarith [this]
  -- the value at the origin
  have hzero := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := F n) (h := f) 0 (hF n) hf
  have hzero' : |a * selfConvolution (F n) 0 - a * selfConvolution f 0| ≤ s n * (|a| * Bc) := by
    have hrw : a * selfConvolution (F n) 0 - a * selfConvolution f 0
        = a * (selfConvolution (F n) 0 - selfConvolution f 0) := by ring
    rw [hrw, abs_mul]
    have h1 : |selfConvolution (F n) 0 - selfConvolution f 0| ≤ s n * Bc := le_trans hzero hKle
    nlinarith [abs_nonneg a, hsnn n, hBcnn]
  -- prime channel
  have hprime := Cvs.WeilForm.PrimeChannelL2Continuous.abs_primeSide_sub_le P R (hF n) hf
  have hprime' : |primePowerSideTruncated P R (selfConvolution (F n))
      - primePowerSideTruncated P R (selfConvolution f)|
      ≤ s n * (2 * Bc * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R) := by
    refine le_trans hprime ?_
    nlinarith [hKle, hmassnn, hsnn n, hBcnn]
  -- assemble
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq]
  have hp := abs_le.mp hpole'
  have hz := abs_le.mp hzero'
  have hpr := abs_le.mp hprime'
  have hAf : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution f 0 - selfConvolution f (u / 2)) := rfl
  have hAFn : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution (F n) 0 - selfConvolution (F n) (u / 2)) := rfl
  rw [hAf, hAFn] at harchn
  have hMsum : s n * M = s n * (2 * Wp * Wn * Bc) + s n * (|a| * Bc)
      + s n * (2 * Bc * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R) := by rw [hM]; ring
  linarith [hp.1, hz.1, hpr.2, harchn, hn, hMsum]

end Cvs.WeilForm.WindowFormLowerSemicontinuous
