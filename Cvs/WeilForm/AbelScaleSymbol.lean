import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BandFreeLogTwoBase
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.VonMangoldtMultiplier
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Continuous Mean Symbol, Abel Scale Multiplier `abelScaleSymbol`, and Lipschitz Bounds

Splits `poleSymbol` into `greenSymbol + meanSymbol`, constructs `abelScaleSymbol` cancelling the
`4 √x` pole–prime growth at `t = 0`, and bounds `abelDiffCosSymbol` by its Lipschitz slope and amplitude.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.AbelScaleSymbol
open Cvs.ZeroCounting

/-! ### 1. Continuous Mean Symbol `meanSymbol` and Truncated Green Symbol `greenSymbol` -/

/-- Explicit antiderivative of `v ↦ 2 exp(v / 2) cos(t v)`. -/
def meanCosAntideriv (t v : ℝ) : ℝ :=
  (4 * Real.exp (v / 2) * Real.cos (t * v) + 8 * t * Real.exp (v / 2) * Real.sin (t * v))
    / (1 + 4 * t ^ 2)

/-- `v ↦ meanCosAntideriv t v` has derivative `2 exp(v / 2) cos(t v)`. -/
theorem hasDerivAt_meanCosAntideriv (t v : ℝ) :
    HasDerivAt (meanCosAntideriv t) (2 * Real.exp (v / 2) * Real.cos (t * v)) v := by
  have hu : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) v := by
    simpa using (hasDerivAt_id v).div_const (2 : ℝ)
  have hv : HasDerivAt (fun u : ℝ => t * u) t v := by
    simpa using (hasDerivAt_id v).const_mul t
  have hnum : HasDerivAt
      (fun u : ℝ => 4 * Real.exp (u / 2) * Real.cos (t * u)
        + 8 * t * Real.exp (u / 2) * Real.sin (t * u))
      ((4 * (Real.exp (v / 2) * (1 / 2)) * Real.cos (t * v)
          + 4 * Real.exp (v / 2) * (-Real.sin (t * v) * t))
        + (8 * t * (Real.exp (v / 2) * (1 / 2)) * Real.sin (t * v)
          + 8 * t * Real.exp (v / 2) * (Real.cos (t * v) * t))) v :=
    ((hu.exp.const_mul 4).mul hv.cos).add ((hu.exp.const_mul (8 * t)).mul hv.sin)
  have hden : 1 + 4 * t ^ 2 ≠ 0 := by positivity
  have hd : ((4 * (Real.exp (v / 2) * (1 / 2)) * Real.cos (t * v)
          + 4 * Real.exp (v / 2) * (-Real.sin (t * v) * t))
        + (8 * t * (Real.exp (v / 2) * (1 / 2)) * Real.sin (t * v)
          + 8 * t * Real.exp (v / 2) * (Real.cos (t * v) * t))) / (1 + 4 * t ^ 2)
      = 2 * Real.exp (v / 2) * Real.cos (t * v) := by
    rw [div_eq_iff hden]; ring
  rw [← hd]
  exact hnum.div_const _

/-- Interval integral of `2 exp(v / 2) cos(t v)` on `[a, b]`. -/
theorem integral_two_mul_exp_half_cos (a b t : ℝ) :
    (∫ v in a..b, 2 * Real.exp (v / 2) * Real.cos (t * v))
      = meanCosAntideriv t b - meanCosAntideriv t a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_meanCosAntideriv t v)
    ((by fun_prop : Continuous fun v : ℝ =>
      2 * Real.exp (v / 2) * Real.cos (t * v)).intervalIntegrable a b)

/-- Continuous prime-mean cosine symbol `∫_0^L 2 e^{v/2} cos(t v) dv`. -/
def meanSymbol (L t : ℝ) : ℝ :=
  (4 * Real.exp (L / 2) * Real.cos (L * t) + 8 * t * Real.exp (L / 2) * Real.sin (L * t) - 4)
    / (1 + 4 * t ^ 2)

/-- Truncated Green cosine symbol `∫_0^L 2 e^{-v/2} cos(t v) dv`. -/
def greenSymbol (L t : ℝ) : ℝ :=
  (4 - 4 * Real.exp (-(L / 2)) * Real.cos (L * t)
      + 8 * t * Real.exp (-(L / 2)) * Real.sin (L * t))
    / (1 + 4 * t ^ 2)

/-- `meanSymbol L t = meanCosAntideriv t L − meanCosAntideriv t 0`. -/
theorem meanSymbol_eq_sub_antideriv (L t : ℝ) :
    meanSymbol L t = meanCosAntideriv t L - meanCosAntideriv t 0 := by
  unfold meanSymbol meanCosAntideriv
  simp only [zero_div, Real.exp_zero, mul_zero, Real.cos_zero, Real.sin_zero]
  rw [mul_comm L t]
  ring

/-- **Integral Representation of `meanSymbol`**:
`meanSymbol L t = ∫_0^L 2 e^{v/2} cos(t v) dv`. -/
theorem meanSymbol_eq_intervalIntegral (L t : ℝ) :
    meanSymbol L t = ∫ v in (0 : ℝ)..L, 2 * Real.exp (v / 2) * Real.cos (t * v) := by
  rw [integral_two_mul_exp_half_cos, ← meanSymbol_eq_sub_antideriv]

/-- **Exact Pole Symbol Split**: `poleSymbol L t = greenSymbol L t + meanSymbol L t`. -/
theorem poleSymbol_eq_greenSymbol_add_meanSymbol (L t : ℝ) :
    Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t = greenSymbol L t + meanSymbol L t := by
  unfold Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol greenSymbol meanSymbol
  rw [Real.sinh_eq, Real.cosh_eq]
  have hden : 1 + 4 * t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### 2. Step-Mean Cosine Symbol & Band-Free Reduction to `abelScaleSymbol` -/

/-- Discrete step-mean cosine symbol `∑_{n=1}^m 4(√(n+1) − √n) cos(t log n)`. -/
def stepMeanCosSymbol (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * Real.cos (t * Real.log n)

/-- `vonMangoldtSymbol x` written as a sum over `Finset.Icc 1 x`. -/
theorem vonMangoldtSymbol_eq_sum_Icc_one (x : ℕ) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t
      = ∑ n ∈ Finset.Icc 1 x, 2 * Cvs.WeilForm.BandFreeLogTwoBase.shellWeight n * Real.cos (t * Real.log n) := by
  rw [Cvs.WeilForm.BandFreeLogTwoBase.vonMangoldtSymbol_eq_shellSymbol]
  unfold Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol
  refine Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun n hn hn2 => ?_
  have h1 : n < 2 := by
    have := (Finset.mem_Icc.1 hn).1
    have := (Finset.mem_Icc.1 hn).2
    by_contra hge
    exact hn2 (Finset.mem_Icc.2 ⟨not_lt.mp hge, this⟩)
  rw [Cvs.WeilForm.BandFreeLogTwoBase.shellWeight_eq_zero_of_lt_two h1, mul_zero, zero_mul]

/-- Decomposition of `vonMangoldtSymbol x` (`1 ≤ x`) into `stepMeanCosSymbol (x - 1)`,
`meanFreeCosSymbol (x - 1)`, and the top endpoint term at `x`. -/
theorem vonMangoldtSymbol_eq_stepMean_add_meanFree_add_top {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t
      = stepMeanCosSymbol (x - 1) t + Cvs.WeilForm.BandFreeLogTwoBase.meanFreeCosSymbol (x - 1) t
        + 2 * Cvs.WeilForm.BandFreeLogTwoBase.shellWeight x * Real.cos (t * Real.log x) := by
  rw [vonMangoldtSymbol_eq_sum_Icc_one]
  have hx_eq : (x - 1) + 1 = x := Nat.sub_add_cancel hx
  conv_lhs => rw [← hx_eq]
  rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 (x - 1)), hx_eq]
  unfold stepMeanCosSymbol Cvs.WeilForm.BandFreeLogTwoBase.meanFreeCosSymbol
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold Cvs.WeilForm.BandFreeLogTwoBase.meanFreeWeight
  ring

/-- **Full Abel Decomposition of `vonMangoldtSymbol x`** (`1 ≤ x`): splits into
`stepMeanCosSymbol (x - 1) + abelDiffCosSymbol (x - 1)` plus a single boundary cosine at `log x`. -/
theorem vonMangoldtSymbol_eq_stepMean_add_abelDiff_add_boundary {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t
      = stepMeanCosSymbol (x - 1) t + Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol (x - 1) t
        + 2 * (Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy (x - 1) + Cvs.WeilForm.BandFreeLogTwoBase.shellWeight x)
            * Real.cos (t * Real.log x) := by
  rw [vonMangoldtSymbol_eq_stepMean_add_meanFree_add_top hx,
    Cvs.WeilForm.BandFreeLogTwoBase.meanFreeCosSymbol_eq_boundary_add_abelDiff (x - 1) t,
    Nat.sub_add_cancel hx]
  ring

/-- **Abel-Reduced Window Multiplier `abelScaleSymbol x`**: replaces `vonMangoldtSymbol x` by
`stepMeanCosSymbol (x - 1) + abelDiffCosSymbol (x - 1)` (dropping the band-free boundary cosine at `log x`). -/
def abelScaleSymbol (x : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol (Real.log x) t + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
    - (stepMeanCosSymbol (x - 1) t + Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol (x - 1) t)

/-- Pointwise difference between `scaleSymbol x` and `abelScaleSymbol x` (`1 ≤ x`). -/
theorem scaleSymbol_sub_abelScaleSymbol_eq {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t - abelScaleSymbol x t
      = -2 * (Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy (x - 1) + Cvs.WeilForm.BandFreeLogTwoBase.shellWeight x)
          * Real.cos (t * Real.log x) := by
  unfold Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol abelScaleSymbol
  rw [vonMangoldtSymbol_eq_stepMean_add_abelDiff_add_boundary hx]
  ring

/-- `scaleSymbol x − abelScaleSymbol x` lies in `bandFree (log x)` for `1 ≤ x`. -/
theorem scaleSymbol_sub_abelScaleSymbol_mem_bandFree {x : ℕ} (hx : 1 ≤ x) :
    (fun t => Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t - abelScaleSymbol x t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) := by
  have heq : (fun t => Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t - abelScaleSymbol x t)
      = (-2 * (Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy (x - 1) + Cvs.WeilForm.BandFreeLogTwoBase.shellWeight x)) •
          fun t => Real.cos (t * Real.log x) := by
    funext t
    rw [scaleSymbol_sub_abelScaleSymbol_eq hx, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact Submodule.smul_mem _ _ (Cvs.WeilForm.BandFreedomCosine.cos_mem_bandFree (le_abs_self _))

/-- `abelScaleSymbol x − scaleSymbol x` lies in `bandFree (log x)` for `1 ≤ x`. -/
theorem abelScaleSymbol_sub_scaleSymbol_mem_bandFree {x : ℕ} (hx : 1 ≤ x) :
    (fun t => abelScaleSymbol x t - Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) := by
  convert (Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x)).neg_mem
    (scaleSymbol_sub_abelScaleSymbol_mem_bandFree hx) using 1
  funext t; simp

/-- `abelScaleSymbol x * rho w` is integrable on `Dom x` (`1 ≤ x`). -/
theorem integrable_abelScaleSymbol_mul_rho {x : ℕ} (hx : 1 ≤ x) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Integrable fun t => abelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have hΦ : Integrable fun t => Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    simpa only [Cvs.WeilForm.AdmissibleMultiplierMinorants.formSpec_self] using
      Cvs.WeilForm.AdmissibleMultiplierMinorants.mem_admissible.1 (Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol_mem_admissible x) w w
  have hb := Cvs.WeilForm.EvenBulkVisibility.integrable_bandFree_mul_rho
    (abelScaleSymbol_sub_scaleSymbol_mem_bandFree hx) w
  refine (hΦ.add hb).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

/-- **Exact Spectral Identity for `abelScaleSymbol`**: on `Dom x` (`1 ≤ x`),
`Qx x w = ∫ t, abelScaleSymbol x t * rho w t`. -/
theorem Qx_eq_integral_abelScaleSymbol {x : ℕ} (hx : 1 ≤ x) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, abelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have hΦ : Integrable fun t => Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    simpa only [Cvs.WeilForm.AdmissibleMultiplierMinorants.formSpec_self] using
      Cvs.WeilForm.AdmissibleMultiplierMinorants.mem_admissible.1 (Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol_mem_admissible x) w w
  have hb := abelScaleSymbol_sub_scaleSymbol_mem_bandFree hx
  have hsplit : (fun t => abelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
      = fun t => Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t
          + (abelScaleSymbol x t - Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t) * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    funext t; ring
  rw [hsplit, integral_add hΦ (Cvs.WeilForm.EvenBulkVisibility.integrable_bandFree_mul_rho hb w),
    Cvs.WeilForm.EvenBulkVisibility.integral_bandFree_mul_rho hb w, add_zero, ← Cvs.WeilForm.VonMangoldtMultiplier.Qx_eq_integral]

/-! ### 3. Lipschitz and Uniform Amplitude Bounds on `abelDiffCosSymbol` -/

/-- Pointwise Lipschitz bound on each logarithmic cosine step (`1 ≤ n`):
`|cos(t log n) − cos(t log(n+1))| ≤ |t| (log(n+1) − log n)`. -/
theorem abs_cos_log_sub_cos_log_succ_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |Real.cos (t * Real.log n) - Real.cos (t * Real.log (n + 1))|
      ≤ |t| * (Real.log (n + 1) - Real.log n) := by
  rw [Cvs.WeilForm.BandFreeLogTwoBase.cos_log_sub_cos_log_succ, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |Real.sin (t * ((Real.log (n + 1) - Real.log n) / 2))|
      ≤ |t * ((Real.log (n + 1) - Real.log n) / 2)| := Real.abs_sin_le_abs
  have h2 : |Real.sin (t * ((Real.log n + Real.log (n + 1)) / 2))| ≤ 1 :=
    Real.abs_sin_le_one _
  have hlog : 0 ≤ Real.log (n + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have harg : |t * ((Real.log (n + 1) - Real.log n) / 2)|
      = |t| * ((Real.log (n + 1) - Real.log n) / 2) := by
    rw [abs_mul, abs_div, abs_of_nonneg hlog, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [harg] at h1
  nlinarith [abs_nonneg (Real.sin (t * ((Real.log (n + 1) - Real.log n) / 2))),
    abs_nonneg (Real.sin (t * ((Real.log n + Real.log (n + 1)) / 2)))]

/-- Pointwise amplitude bound `|cos(t log n) − cos(t log(n+1))| ≤ 2`. -/
theorem abs_cos_log_sub_cos_log_succ_le_two (n : ℕ) (t : ℝ) :
    |Real.cos (t * Real.log n) - Real.cos (t * Real.log (n + 1))| ≤ 2 := by
  refine (abs_sub _ _).trans ?_
  linarith [Real.abs_cos_le_one (t * Real.log n), Real.abs_cos_le_one (t * Real.log (n + 1))]

/-- Cumulative Lipschitz slope `∑_{n=1}^m 2 |D(n)| (log(n+1) − log n)` of `abelDiffCosSymbol m`. -/
def abelLipSlope (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, 2 * |Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy n| * (Real.log (n + 1) - Real.log n)

/-- Uniform amplitude bound `∑_{n=1}^m 4 |D(n)|` on `abelDiffCosSymbol m`. -/
def abelMaxAmp (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, 4 * |Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy n|

theorem abelLipSlope_nonneg (m : ℕ) : 0 ≤ abelLipSlope m := by
  unfold abelLipSlope
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hlog : 0 ≤ Real.log (n + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn1) (by linarith))
  positivity

theorem abelMaxAmp_nonneg (m : ℕ) : 0 ≤ abelMaxAmp m := by
  unfold abelMaxAmp
  exact Finset.sum_nonneg fun _ _ => by positivity

/-- **Small-`|t|` Lipschitz Bound on `abelDiffCosSymbol`**:
`|abelDiffCosSymbol m t| ≤ abelLipSlope m * |t|`. -/
theorem abs_abelDiffCosSymbol_le_lip (m : ℕ) (t : ℝ) :
    |Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol m t| ≤ abelLipSlope m * |t| := by
  unfold Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol abelLipSlope
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hstep := abs_cos_log_sub_cos_log_succ_le hn1 t
  have hmul := mul_le_mul_of_nonneg_left hstep
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) (abs_nonneg (Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy n)))
  linarith

/-- **Uniform Amplitude Bound on `abelDiffCosSymbol`**:
`|abelDiffCosSymbol m t| ≤ abelMaxAmp m`. -/
theorem abs_abelDiffCosSymbol_le_amp (m : ℕ) (t : ℝ) :
    |Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol m t| ≤ abelMaxAmp m := by
  unfold Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol abelMaxAmp
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hstep := abs_cos_log_sub_cos_log_succ_le_two n t
  have hmul := mul_le_mul_of_nonneg_left hstep
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) (abs_nonneg (Cvs.WeilForm.BandFreeLogTwoBase.cumMeanFreeDiscrepancy n)))
  linarith

end Cvs.WeilForm.AbelScaleSymbol
