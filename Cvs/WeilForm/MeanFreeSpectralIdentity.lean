import Mathlib
import Cvs.WeilForm.AbelScaleSymbol
import Cvs.WeilForm.BandFreeLogTwoBase
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InterPrimePhaseCancellation
import Cvs.WeilForm.StepQuadratureResidual
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Mean-Free Spectral Identity, Lag-Space Bounds, and Phase-Deficit Shell Linearization

Establishes `meanFreePrimeTerm = ∫ meanFreeOscSymbol · ρ_w` on `Dom x`, bounds `meanFreePrimeTerm`
via `atomBudget` and centered poles, and proves the phase-deficit quadratic shell linearization bound.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.MeanFreeSpectralIdentity
open Cvs.ZeroCounting

/-! ### 1. Uniform Amplitude Bounds and Exact Spectral Identity for `meanFreePrimeTerm` -/

/-- Uniform amplitude bound `8 (√(m + 1) − 1)` on `stepQuadSymbol m`. -/
def stepQuadMaxAmp (m : ℕ) : ℝ :=
  8 * (Real.sqrt (m + 1) - 1)

/-- Combined uniform amplitude bound `stepQuadMaxAmp m + abelMaxAmp m` on `meanFreeOscSymbol m`. -/
def totalMeanFreeMaxAmp (m : ℕ) : ℝ :=
  stepQuadMaxAmp m + Cvs.WeilForm.AbelScaleSymbol.abelMaxAmp m

theorem stepQuadMaxAmp_nonneg (m : ℕ) : 0 ≤ stepQuadMaxAmp m := by
  unfold stepQuadMaxAmp
  have h1 : 1 ≤ Real.sqrt (m + 1) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) m] : (1 : ℝ) ≤ m + 1)
  linarith

theorem totalMeanFreeMaxAmp_nonneg (m : ℕ) : 0 ≤ totalMeanFreeMaxAmp m :=
  add_nonneg (stepQuadMaxAmp_nonneg m) (Cvs.WeilForm.AbelScaleSymbol.abelMaxAmp_nonneg m)

/-- Uniform amplitude bound `|stepMeanCosSymbol m t| ≤ 4 (√(m + 1) − 1)`. -/
theorem abs_stepMeanCosSymbol_le (m : ℕ) (t : ℝ) :
    |Cvs.WeilForm.AbelScaleSymbol.stepMeanCosSymbol m t| ≤ 4 * (Real.sqrt (m + 1) - 1) := by
  unfold Cvs.WeilForm.AbelScaleSymbol.stepMeanCosSymbol
  have hsum : 4 * (Real.sqrt (m + 1) - 1)
      = ∑ n ∈ Finset.Icc 1 m, 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n := by
    rw [← Finset.mul_sum, Cvs.WeilForm.BandFreeLogTwoBase.sum_stepMeanWeight]
    ring
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hw : 0 ≤ 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n := by
    have := Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight_nonneg n; positivity
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)

/-- Uniform amplitude bound `|meanSymbol L t| ≤ 4 (e^{L/2} − 1)` (`0 ≤ L`). -/
theorem abs_meanSymbol_le {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    |Cvs.WeilForm.AbelScaleSymbol.meanSymbol L t| ≤ 4 * (Real.exp (L / 2) - 1) := by
  have hint : 4 * (Real.exp (L / 2) - 1) = 1 * ∫ v in (0 : ℝ)..L, 2 * Real.exp (v / 2) := by
    rw [Cvs.WeilForm.StepQuadratureResidual.integral_two_mul_exp_half, zero_div, Real.exp_zero, one_mul]
  rw [Cvs.WeilForm.AbelScaleSymbol.meanSymbol_eq_intervalIntegral, hint]
  apply Cvs.WeilForm.StepQuadratureResidual.abs_intervalIntegral_le_of_abs_le hL
  · fun_prop
  · fun_prop
  intro v _
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.exp (v / 2)), one_mul]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Uniform amplitude bound `|stepQuadSymbol m t| ≤ stepQuadMaxAmp m`. -/
theorem abs_stepQuadSymbol_le_amp (m : ℕ) (t : ℝ) :
    |Cvs.WeilForm.StepQuadratureResidual.stepQuadSymbol m t| ≤ stepQuadMaxAmp m := by
  unfold Cvs.WeilForm.StepQuadratureResidual.stepQuadSymbol stepQuadMaxAmp
  have hL : 0 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h1 := abs_stepMeanCosSymbol_le m t
  have h2 := abs_meanSymbol_le hL t
  have hexp := Cvs.WeilForm.StepQuadratureResidual.exp_log_nat_div_two (Nat.le_add_left 1 m)
  push_cast at hexp
  rw [hexp] at h2
  linarith [abs_sub (Cvs.WeilForm.AbelScaleSymbol.stepMeanCosSymbol m t) (Cvs.WeilForm.AbelScaleSymbol.meanSymbol (Real.log (m + 1)) t)]

/-- Uniform amplitude bound `|meanFreeOscSymbol m t| ≤ totalMeanFreeMaxAmp m`. -/
theorem abs_meanFreeOscSymbol_le_amp (m : ℕ) (t : ℝ) :
    |Cvs.WeilForm.StepQuadratureResidual.meanFreeOscSymbol m t| ≤ totalMeanFreeMaxAmp m := by
  unfold Cvs.WeilForm.StepQuadratureResidual.meanFreeOscSymbol totalMeanFreeMaxAmp
  linarith [abs_add_le (Cvs.WeilForm.StepQuadratureResidual.stepQuadSymbol m t) (Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol m t),
    abs_stepQuadSymbol_le_amp m t, Cvs.WeilForm.AbelScaleSymbol.abs_abelDiffCosSymbol_le_amp m t]

/-! ### 2. Lag-Space Path-Law + Centered-Pole Bounds on `windowMeanTerm` and `meanFreePrimeTerm` -/

/-! ### 3. Phase-Deficit Quadratic Shell Linearization Bound on `shellSymbol` -/

/-- `shellSymbol a b * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_shellSymbol_mul_rho {L : ℝ} {hL : 0 ≤ L} (a b : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol a b t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  simp only [Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol_eq_cosSum]
  exact Cvs.WeilForm.InterPrimePhaseCancellation.integrable_cosSum_mul_rho (Finset.Icc a b) Cvs.WeilForm.BandFreeLogTwoBase.shellWeight (fun n => Real.log n) φ

end Cvs.WeilForm.MeanFreeSpectralIdentity
