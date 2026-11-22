import Mathlib
import Cvs.Finite.GridFrequencySums
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The coefficients are the samples

Read at a frequency the sum carries, every exponential but one spans a whole number of periods of
the window and integrates away. The survivor is the mode whose label is the opposite, and evenness
returns it to the frequency asked for, so the transform there is the window length times that
coefficient, and recentring turns it by a half-turn for each unit of the label.
-/

noncomputable section

open Real

namespace Cvs.Finite.CoefficientsAreSamples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An exponential spanning a whole number of periods integrates away. -/
theorem integral_exp_eq_zero {L : ℝ} {c : ℂ} (hc : c ≠ 0)
    (hcL : Complex.exp (c * (L : ℂ)) = 1) (a : ℂ) :
    ∫ t in (0 : ℝ)..L, a * Complex.exp (c * (t : ℂ)) = 0 := by
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc, hcL]
  simp

/-- At the matching label the exponential is trivial and the integral is the window length. -/
theorem integral_exp_eq_const {L : ℝ} (a : ℂ) :
    ∫ t in (0 : ℝ)..L, a * Complex.exp ((0 : ℂ) * (t : ℂ)) = (L : ℂ) * a := by
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_const]
  simp [Complex.real_smul]

/-- **The transform at a carried frequency is the window length times that coefficient.** -/
theorem fourierLaplace_at_grid {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    (hinj : Function.Injective mode)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) (j : ι) :
    FourierLaplace.fourierLaplace
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))
        ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)
      = (L : ℂ) * (xi j : ℂ) := by
  set z : ℂ := ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) with hzdef
  have hInd : ∀ t : ℝ, Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) t
        * Complex.exp (Complex.I * z * (t : ℂ))
      = Set.indicator (Set.Ioc (0 : ℝ) L)
          (fun t : ℝ => (∑ i, (xi i : ℂ)
              * Complex.exp (Complex.I
                  * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) * (t : ℂ)))) t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) L
    · rw [Set.indicator_of_mem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, if_pos ht]
      rw [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum_eq_exp_sum hinv hmode hxieven t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      ring_nf
    · rw [Set.indicator_of_notMem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, if_neg ht]
      simp
  have hint : ∀ i : ι, IntervalIntegrable
      (fun t : ℝ => (xi i : ℂ)
        * Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z)
            * (t : ℂ)))
      MeasureTheory.volume 0 L := fun i =>
    (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable 0 L
  have hdiagz : ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode (neg j) : ℝ) : ℂ) + z = 0 := by
    rw [hzdef, Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode j]
    push_cast
    ring
  have hoff : ∀ i ∈ (Finset.univ : Finset ι), i ≠ neg j →
      (∫ t in (0 : ℝ)..L, (xi i : ℂ)
        * Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z)
            * (t : ℂ))) = 0 := by
    intro i _ hi
    have hne : ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
      intro hcon
      rw [hzdef] at hcon
      have hlab := (Cvs.Finite.GridFrequencySums.omega_add_eq_zero_iff (ne_of_gt hL) mode i j).mp hcon
      have hmj : mode i = mode (neg j) := by rw [hmode j]; omega
      exact hi (hinj hmj)
    refine integral_exp_eq_zero (mul_ne_zero Complex.I_ne_zero hne) ?_ _
    rw [hzdef]
    exact Cvs.Finite.GridFrequencySums.exp_omega_add_mul (ne_of_gt hL) mode i j
  rw [FourierLaplace.fourierLaplace]
  simp only [hInd]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hL.le,
    intervalIntegral.integral_finsetSum (fun i _ => hint i),
    Finset.sum_eq_single_of_mem (neg j) (Finset.mem_univ _) hoff, hdiagz, mul_zero,
    integral_exp_eq_const, hxieven j]

/-- **The recentred transform at a carried frequency is that coefficient, up to a half-turn.** -/
theorem centred_at_grid {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    (hinj : Function.Injective mode)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) (j : ι) :
    Complex.exp (-(Complex.I * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) * (L : ℂ) / 2))
        * FourierLaplace.fourierLaplace
            (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))
            ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)
      = (-1 : ℂ) ^ (mode j) * ((L : ℂ) * (xi j : ℂ)) := by
  rw [fourierLaplace_at_grid hL hinv hmode hinj hxieven j,
    Cvs.Finite.GridFrequencySums.phase_at_grid (ne_of_gt hL) mode j]

end Cvs.Finite.CoefficientsAreSamples
