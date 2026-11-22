import Mathlib
import Cvs.WeilForm.AbelScaleSymbol
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BandFreeLogTwoBase
import Cvs.WeilForm.PolePrimeCosineMultipliers

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Truncated Green Integral, Step-Quadrature Residual `stepQuadSymbol`, and Origin Coercivity

Proves the integral representation and Lipschitz bounds for `greenSymbol`, the step-quadrature
residual `stepQuadSymbol` and its Lipschitz bound, and the origin lower bound on `abelScaleSymbol`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.StepQuadratureResidual
open Cvs.ZeroCounting

/-! ### 1. Integral Representation and Lipschitz Bounds for `greenSymbol` -/

/-- Product-to-sum identity `cos a − cos b = −2 sin((a − b)/2) sin((a + b)/2)`. -/
theorem cos_sub_cos_eq (a b : ℝ) :
    Real.cos a - Real.cos b = -2 * Real.sin ((a - b) / 2) * Real.sin ((a + b) / 2) := by
  have ha : Real.cos a = Real.cos ((a + b) / 2 + (a - b) / 2) := by congr 1; ring
  have hb : Real.cos b = Real.cos ((a + b) / 2 - (a - b) / 2) := by congr 1; ring
  rw [ha, hb, Real.cos_add, Real.cos_sub]
  ring

/-- Global 1-Lipschitz bound `|cos a − cos b| ≤ |a − b|`. -/
theorem abs_cos_sub_cos_le (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| := by
  rw [cos_sub_cos_eq, abs_mul, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
  have h1 : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  have h2 : |Real.sin ((a + b) / 2)| ≤ 1 := Real.abs_sin_le_one _
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
  nlinarith [abs_nonneg (Real.sin ((a - b) / 2)), abs_nonneg (Real.sin ((a + b) / 2))]

/-- Pointwise Lipschitz bound `|cos x − 1| ≤ |x|`. -/
theorem abs_cos_sub_one_le (x : ℝ) : |Real.cos x - 1| ≤ |x| := by
  simpa only [Real.cos_zero, sub_zero] using abs_cos_sub_cos_le x 0

/-- Explicit antiderivative of `v ↦ 2 exp(−v / 2) cos(t v)`. -/
def greenCosAntideriv (t v : ℝ) : ℝ :=
  (-4 * Real.exp (-(v / 2)) * Real.cos (t * v) + 8 * t * Real.exp (-(v / 2)) * Real.sin (t * v))
    / (1 + 4 * t ^ 2)

/-- `v ↦ greenCosAntideriv t v` has derivative `2 exp(−v / 2) cos(t v)`. -/
theorem hasDerivAt_greenCosAntideriv (t v : ℝ) :
    HasDerivAt (greenCosAntideriv t) (2 * Real.exp (-(v / 2)) * Real.cos (t * v)) v := by
  have hu : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) v :=
    ((hasDerivAt_id v).div_const (2 : ℝ)).neg
  have hv : HasDerivAt (fun u : ℝ => t * u) t v := by
    simpa using (hasDerivAt_id v).const_mul t
  have hnum : HasDerivAt
      (fun u : ℝ => -4 * Real.exp (-(u / 2)) * Real.cos (t * u)
        + 8 * t * Real.exp (-(u / 2)) * Real.sin (t * u))
      ((-4 * (Real.exp (-(v / 2)) * -(1 / 2)) * Real.cos (t * v)
          + -4 * Real.exp (-(v / 2)) * (-Real.sin (t * v) * t))
        + (8 * t * (Real.exp (-(v / 2)) * -(1 / 2)) * Real.sin (t * v)
          + 8 * t * Real.exp (-(v / 2)) * (Real.cos (t * v) * t))) v :=
    ((hu.exp.const_mul (-4)).mul hv.cos).add ((hu.exp.const_mul (8 * t)).mul hv.sin)
  have hden : 1 + 4 * t ^ 2 ≠ 0 := by positivity
  have hd : ((-4 * (Real.exp (-(v / 2)) * -(1 / 2)) * Real.cos (t * v)
          + -4 * Real.exp (-(v / 2)) * (-Real.sin (t * v) * t))
        + (8 * t * (Real.exp (-(v / 2)) * -(1 / 2)) * Real.sin (t * v)
          + 8 * t * Real.exp (-(v / 2)) * (Real.cos (t * v) * t))) / (1 + 4 * t ^ 2)
      = 2 * Real.exp (-(v / 2)) * Real.cos (t * v) := by
    rw [div_eq_iff hden]; ring
  rw [← hd]
  exact hnum.div_const _

/-- Interval integral of `2 exp(−v / 2) cos(t v)` on `[a, b]`. -/
theorem integral_two_mul_exp_neg_half_cos (a b t : ℝ) :
    (∫ v in a..b, 2 * Real.exp (-(v / 2)) * Real.cos (t * v))
      = greenCosAntideriv t b - greenCosAntideriv t a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_greenCosAntideriv t v)
    ((by fun_prop : Continuous fun v : ℝ =>
      2 * Real.exp (-(v / 2)) * Real.cos (t * v)).intervalIntegrable a b)

/-- `greenSymbol L t = greenCosAntideriv t L − greenCosAntideriv t 0`. -/
theorem greenSymbol_eq_sub_antideriv (L t : ℝ) :
    Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t = greenCosAntideriv t L - greenCosAntideriv t 0 := by
  unfold Cvs.WeilForm.AbelScaleSymbol.greenSymbol greenCosAntideriv
  simp only [zero_div, neg_zero, Real.exp_zero, mul_zero, Real.cos_zero, Real.sin_zero]
  rw [mul_comm L t]
  ring

/-- **Integral Representation of `greenSymbol`**:
`greenSymbol L t = ∫_0^L 2 e^{-v/2} cos(t v) dv`. -/
theorem greenSymbol_eq_intervalIntegral (L t : ℝ) :
    Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t = ∫ v in (0 : ℝ)..L, 2 * Real.exp (-(v / 2)) * Real.cos (t * v) := by
  rw [integral_two_mul_exp_neg_half_cos, ← greenSymbol_eq_sub_antideriv]

/-- Interval integral absolute-value bound against a continuous majorant `C * g`. -/
theorem abs_intervalIntegral_le_of_abs_le {a b C : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hg : Continuous g)
    (hbound : ∀ v ∈ Set.Icc a b, |f v| ≤ C * g v) :
    |∫ v in a..b, f v| ≤ C * ∫ v in a..b, g v := by
  rw [abs_le, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  constructor
  · exact intervalIntegral.integral_mono_on hab
      ((hg.const_mul C).neg.intervalIntegrable a b) (hf.intervalIntegrable a b)
      fun v hv => (abs_le.mp (hbound v hv)).1
  · exact intervalIntegral.integral_mono_on hab
      (hf.intervalIntegrable a b) ((hg.const_mul C).intervalIntegrable a b)
      fun v hv => (abs_le.mp (hbound v hv)).2

/-! ### 2. Step-Quadrature Residual `stepQuadSymbol` and Universal Lipschitz Bound -/

/-- Interval integral of `2 exp(v / 2)` on `[a, b]`. -/
theorem integral_two_mul_exp_half (a b : ℝ) :
    (∫ v in a..b, 2 * Real.exp (v / 2)) = 4 * (Real.exp (b / 2) - Real.exp (a / 2)) := by
  have h := Cvs.WeilForm.AbelScaleSymbol.integral_two_mul_exp_half_cos a b 0
  simp only [zero_mul, Real.cos_zero, mul_one, Cvs.WeilForm.AbelScaleSymbol.meanCosAntideriv,
    Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  rw [h]
  ring

/-- For `1 ≤ n`, `exp(log n / 2) = √n`. -/
theorem exp_log_nat_div_two {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (Real.log n / 2) = Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.mpr hn0)]

/-- Exact logarithmic step integral `∫_{log n}^{log(n+1)} 2 e^{v/2} dv = 2 stepMeanWeight n`. -/
theorem integral_step_two_mul_exp_half {n : ℕ} (hn : 1 ≤ n) :
    (∫ v in Real.log n..Real.log (n + 1), 2 * Real.exp (v / 2))
      = 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n := by
  have h1 : (∫ v in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), 2 * Real.exp (v / 2))
      = 4 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
    rw [integral_two_mul_exp_half, exp_log_nat_div_two hn,
      exp_log_nat_div_two (Nat.le_add_left 1 n)]
  push_cast at h1
  rw [h1]
  unfold Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight
  ring

/-- Telescoping decomposition of `meanSymbol (log(m + 1))` into step integrals on `[log n, log(n+1)]`. -/
theorem sum_step_integral_cos_eq_meanSymbol (m : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.Icc 1 m,
        (∫ v in Real.log n..Real.log (n + 1), 2 * Real.exp (v / 2) * Real.cos (t * v))
      = Cvs.WeilForm.AbelScaleSymbol.meanSymbol (Real.log (m + 1)) t := by
  induction m with
  | zero =>
    simp [Cvs.WeilForm.AbelScaleSymbol.meanSymbol_eq_sub_antideriv]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 k), ih,
      Cvs.WeilForm.AbelScaleSymbol.meanSymbol_eq_sub_antideriv, Cvs.WeilForm.AbelScaleSymbol.meanSymbol_eq_sub_antideriv,
      Cvs.WeilForm.AbelScaleSymbol.integral_two_mul_exp_half_cos]
    push_cast
    ring

/-- **Step-Quadrature Residual `stepQuadSymbol m`**: the difference between the discrete step-mean
cosine sum `stepMeanCosSymbol m` and the continuous mean integral `meanSymbol (log(m + 1))`. -/
def stepQuadSymbol (m : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.AbelScaleSymbol.stepMeanCosSymbol m t - Cvs.WeilForm.AbelScaleSymbol.meanSymbol (Real.log (m + 1)) t

/-- Cumulative step-quadrature Lipschitz slope `∑_{n=1}^m 2 w̄(n) (log(n+1) − log n)`. -/
def stepQuadLipSlope (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * (Real.log (n + 1) - Real.log n)

theorem stepQuadLipSlope_nonneg (m : ℕ) : 0 ≤ stepQuadLipSlope m := by
  unfold stepQuadLipSlope
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hlog : 0 ≤ Real.log (n + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn1) (by linarith))
  have hw := Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight_nonneg n
  positivity

/-- Step-by-step decomposition of `stepQuadSymbol m`. -/
theorem stepQuadSymbol_eq_sum_step (m : ℕ) (t : ℝ) :
    stepQuadSymbol m t
      = ∑ n ∈ Finset.Icc 1 m,
          (2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * Real.cos (t * Real.log n)
            - ∫ v in Real.log n..Real.log (n + 1), 2 * Real.exp (v / 2) * Real.cos (t * v)) := by
  unfold stepQuadSymbol Cvs.WeilForm.AbelScaleSymbol.stepMeanCosSymbol
  rw [← sum_step_integral_cos_eq_meanSymbol, ← Finset.sum_sub_distrib]

/-- Single-step quadrature Lipschitz bound on `[log n, log(n+1)]` (`1 ≤ n`). -/
theorem abs_step_quad_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * Real.cos (t * Real.log n)
        - ∫ v in Real.log n..Real.log (n + 1), 2 * Real.exp (v / 2) * Real.cos (t * v)|
      ≤ 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * (Real.log (n + 1) - Real.log n) * |t| := by
  have hab : Real.log n ≤ Real.log (n + 1) :=
    Real.log_le_log (by exact_mod_cast hn) (by linarith)
  have hsub : 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * Real.cos (t * Real.log n)
        - (∫ v in Real.log n..Real.log (n + 1), 2 * Real.exp (v / 2) * Real.cos (t * v))
      = ∫ v in Real.log n..Real.log (n + 1),
          2 * Real.exp (v / 2) * (Real.cos (t * Real.log n) - Real.cos (t * v)) := by
    rw [← integral_step_two_mul_exp_half hn, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  rw [hsub, show 2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n * (Real.log (n + 1) - Real.log n) * |t|
    = ((Real.log (n + 1) - Real.log n) * |t|) * (2 * Cvs.WeilForm.BandFreeLogTwoBase.stepMeanWeight n) by ring,
    ← integral_step_two_mul_exp_half hn]
  apply abs_intervalIntegral_le_of_abs_le hab
  · fun_prop
  · fun_prop
  intro v hv
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.exp (v / 2))]
  have hcos : |Real.cos (t * Real.log n) - Real.cos (t * v)|
      ≤ (Real.log (n + 1) - Real.log n) * |t| := by
    refine (abs_cos_sub_cos_le _ _).trans ?_
    rw [show t * Real.log n - t * v = -t * (v - Real.log n) by ring,
      abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hv.1), mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith [hv.2]) (abs_nonneg t)
  linarith [mul_le_mul_of_nonneg_left hcos (by positivity : 0 ≤ 2 * Real.exp (v / 2))]

/-- **Universal Lipschitz Bound on `stepQuadSymbol`**:
`|stepQuadSymbol m t| ≤ stepQuadLipSlope m * |t|`. -/
theorem abs_stepQuadSymbol_le_lip (m : ℕ) (t : ℝ) :
    |stepQuadSymbol m t| ≤ stepQuadLipSlope m * |t| := by
  rw [stepQuadSymbol_eq_sum_step]
  unfold stepQuadLipSlope
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  exact abs_step_quad_le (Finset.mem_Icc.1 hn).1 t

/-! ### 3. Complete Mean-Free Decomposition of `abelScaleSymbol` & Origin Coercivity -/

/-- Total oscillatory residual `stepQuadSymbol m + abelDiffCosSymbol m` after subtracting `meanSymbol`. -/
def meanFreeOscSymbol (m : ℕ) (t : ℝ) : ℝ :=
  stepQuadSymbol m t + Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol m t

/-- Combined Lipschitz slope `stepQuadLipSlope m + abelLipSlope m` of `meanFreeOscSymbol m`. -/
def totalMeanFreeSlope (m : ℕ) : ℝ :=
  stepQuadLipSlope m + Cvs.WeilForm.AbelScaleSymbol.abelLipSlope m

theorem totalMeanFreeSlope_nonneg (m : ℕ) : 0 ≤ totalMeanFreeSlope m :=
  add_nonneg (stepQuadLipSlope_nonneg m) (Cvs.WeilForm.AbelScaleSymbol.abelLipSlope_nonneg m)

/-- Lipschitz bound `|meanFreeOscSymbol m t| ≤ totalMeanFreeSlope m * |t|`. -/
theorem abs_meanFreeOscSymbol_le_lip (m : ℕ) (t : ℝ) :
    |meanFreeOscSymbol m t| ≤ totalMeanFreeSlope m * |t| := by
  unfold meanFreeOscSymbol totalMeanFreeSlope
  refine (abs_add_le _ _).trans ?_
  linarith [abs_stepQuadSymbol_le_lip m t, Cvs.WeilForm.AbelScaleSymbol.abs_abelDiffCosSymbol_le_lip m t]

/-- **Mean-Cancelled Decomposition of `abelScaleSymbol`** (`1 ≤ x`):
`meanSymbol (log x)` cancels between `poleSymbol (log x)` and `stepMeanCosSymbol (x - 1)`,
leaving `archSymbol + greenSymbol (log x) − stepQuadSymbol (x - 1) − abelDiffCosSymbol (x - 1)`. -/
theorem abelScaleSymbol_eq_arch_add_green_sub {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    Cvs.WeilForm.AbelScaleSymbol.abelScaleSymbol x t
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t + Cvs.WeilForm.AbelScaleSymbol.greenSymbol (Real.log x) t
        - stepQuadSymbol (x - 1) t - Cvs.WeilForm.BandFreeLogTwoBase.abelDiffCosSymbol (x - 1) t := by
  unfold Cvs.WeilForm.AbelScaleSymbol.abelScaleSymbol stepQuadSymbol
  have hcast : ((x - 1 : ℕ) : ℝ) + 1 = x := by exact_mod_cast Nat.sub_add_cancel hx
  rw [Cvs.WeilForm.AbelScaleSymbol.poleSymbol_eq_greenSymbol_add_meanSymbol (Real.log x) t, hcast]
  ring

/-- Compact mean-cancelled decomposition `abelScaleSymbol x = archSymbol + greenSymbol − meanFreeOscSymbol`. -/
theorem abelScaleSymbol_eq_arch_add_green_sub_osc {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    Cvs.WeilForm.AbelScaleSymbol.abelScaleSymbol x t
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t + Cvs.WeilForm.AbelScaleSymbol.greenSymbol (Real.log x) t
        - meanFreeOscSymbol (x - 1) t := by
  rw [abelScaleSymbol_eq_arch_add_green_sub hx t]
  unfold meanFreeOscSymbol
  ring

end Cvs.WeilForm.StepQuadratureResidual
