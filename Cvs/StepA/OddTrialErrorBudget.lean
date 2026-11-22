import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.OddTrialEnvelope
import Cvs.StepA.OffLineZeroTrade
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.SectorGramBoxTransform
import Cvs.StepA.SineModeOddTrial
import Cvs.StepA.SineParseval
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The error budget of the odd trial at one zero
For `y = Im z ≠ 0`, `L ≥ 0`: each Bessel defect of `uo z`, `vo z` is `≤ edgeConst² L/(π²(N+1))`, so
`trialBound − lamO ≤ projEnv z (L/(N+1)) e^{|y|L}`, `projEnv z r → 0` as `r → 0`: `o(e^{|y|L})` at
`N = ⌈L²⌉₊`, `≤ projRate z Ω e^{|y|L}` at `N = ⌈ΩL/2π⌉₊`, `projRate z Ω → 0`. The on-line budget at
polynomially many modes, and `lamE L w`, `lamOTop L w` for `|Im w| < c`, are `o(e^{cL})`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Asymptotics

namespace Cvs.StepA.OddTrialErrorBudget
open Cvs.ZeroCounting

open Cvs.StepA.OneZeroParitySectors (ue ve uo vo continuous_ue continuous_ve continuous_uo continuous_vo)
open Cvs.StepA.OneZeroSectorBottoms (lamE lamO sigE sigO hasDerivAt_uo hasDerivAt_vo)
open Cvs.StepA.TopQuadruple (integral_sq_nonneg)
open Cvs.StepA.SineModeOddTrial (projDefect trialBound)
open Cvs.StepA.OddTrialEnvelope (onLineBound)

/-! ### Hyperbolic bounds and the window integral of `cosh` -/

/-- `cosh x ≤ e^{|x|}`. -/
theorem cosh_le_exp_abs (x : ℝ) : cosh x ≤ exp |x| := by
  rw [Real.cosh_eq]
  have h1 : exp x ≤ exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : exp (-x) ≤ exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- `2 sinh x ≤ e^x`. -/
theorem two_mul_sinh_le_exp (x : ℝ) : 2 * sinh x ≤ exp x := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-x)
  linarith

/-- `y ∫_{−L/2}^{L/2} cosh(yt) dt = 2 sinh(yL/2)`, for every `L` and `y`. -/
theorem mul_integral_cosh_mul (L y : ℝ) :
    y * ∫ t in -(L / 2)..L / 2, cosh (y * t) = 2 * sinh (y * L / 2) := by
  have h := Cvs.StepA.SectorGramBoxTransform.mul_integral_cosh_two_mul L (y / 2)
  have e : ∀ t : ℝ, 2 * (y / 2) * t = y * t := fun t => by ring
  simp only [e] at h
  rw [show y * L / 2 = y / 2 * L by ring]
  linear_combination 2 * h

/-- `|y| ∫_{−L/2}^{L/2} cosh(yt) dt = 2 sinh(|y|L/2)`, for every `L` and `y`. -/
theorem abs_mul_integral_cosh_mul (L y : ℝ) :
    |y| * ∫ t in -(L / 2)..L / 2, cosh (y * t) = 2 * sinh (|y| * L / 2) := by
  rcases abs_choice y with h | h
  · rw [h]
    exact mul_integral_cosh_mul L y
  · have e : (∫ t in -(L / 2)..L / 2, cosh (y * t)) = ∫ t in -(L / 2)..L / 2, cosh (-y * t) :=
      intervalIntegral.integral_congr fun t _ => by simp only [neg_mul, Real.cosh_neg]
    rw [h, e]
    exact mul_integral_cosh_mul L (-y)

/-- For `y ≠ 0`, `∫_{−L/2}^{L/2} cosh(yt) dt = 2 sinh(|y|L/2)/|y|`. -/
theorem integral_cosh_mul_eq (L : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in -(L / 2)..L / 2, cosh (y * t) = 2 * sinh (|y| * L / 2) / |y| := by
  rw [eq_div_iff (abs_pos.mpr hy).ne', mul_comm]
  exact abs_mul_integral_cosh_mul L y

/-- For `y ≠ 0`, `∫_{−L/2}^{L/2} cosh(2yt) dt = sinh(|y|L)/|y|`. -/
theorem integral_cosh_two_mul_eq (L : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in -(L / 2)..L / 2, cosh (2 * y * t) = sinh (|y| * L) / |y| := by
  have h := abs_mul_integral_cosh_mul L (2 * y)
  rw [abs_mul, abs_two, show 2 * |y| * L / 2 = |y| * L by ring] at h
  rw [eq_div_iff (abs_pos.mpr hy).ne']
  linear_combination h / 2

/-! ### The sector weights against `cosh` -/

/-- `|ue z t| ≤ cosh(yt)`. -/
theorem abs_ue_le (z : ℂ) (t : ℝ) : |ue z t| ≤ cosh (z.im * t) := by
  unfold ue
  rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
  exact mul_le_of_le_one_left (Real.cosh_pos _).le (Real.abs_cos_le_one _)

/-- `|uo z t| ≤ cosh(yt)`. -/
theorem abs_uo_le (z : ℂ) (t : ℝ) : |uo z t| ≤ cosh (z.im * t) := by
  unfold uo
  rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
  exact mul_le_of_le_one_left (Real.cosh_pos _).le (Real.abs_sin_le_one _)

/-- `|ve z t| ≤ cosh(yt)`. -/
theorem abs_ve_le (z : ℂ) (t : ℝ) : |ve z t| ≤ cosh (z.im * t) := by
  unfold ve
  rw [abs_mul]
  have h1 : |sinh (z.im * t)| ≤ cosh (z.im * t) := by
    rw [Real.abs_sinh, ← Real.cosh_abs (z.im * t)]
    exact (Real.sinh_lt_cosh _).le
  calc |sin (z.re * t)| * |sinh (z.im * t)| ≤ 1 * cosh (z.im * t) :=
        mul_le_mul (Real.abs_sin_le_one _) h1 (abs_nonneg _) zero_le_one
    _ = cosh (z.im * t) := one_mul _

/-- `|vo z t| ≤ cosh(yt)`. -/
theorem abs_vo_le (z : ℂ) (t : ℝ) : |vo z t| ≤ cosh (z.im * t) := by
  unfold vo
  rw [abs_mul]
  have h1 : |sinh (z.im * t)| ≤ cosh (z.im * t) := by
    rw [Real.abs_sinh, ← Real.cosh_abs (z.im * t)]
    exact (Real.sinh_lt_cosh _).le
  calc |cos (z.re * t)| * |sinh (z.im * t)| ≤ 1 * cosh (z.im * t) :=
        mul_le_mul (Real.abs_cos_le_one _) h1 (abs_nonneg _) zero_le_one
    _ = cosh (z.im * t) := one_mul _

/-- The derivative of `uo z` is `x ue + y ve`. -/
theorem deriv_uo (z : ℂ) : deriv (uo z) = fun t => z.re * ue z t + z.im * ve z t :=
  funext fun t => (hasDerivAt_uo z t).deriv

/-- The derivative of `vo z` is `y ue − x ve`. -/
theorem deriv_vo (z : ℂ) : deriv (vo z) = fun t => z.im * ue z t - z.re * ve z t :=
  funext fun t => (hasDerivAt_vo z t).deriv

/-- `|uo'(t)| ≤ (|x| + |y|) cosh(yt)`. -/
theorem abs_deriv_uo_le (z : ℂ) (t : ℝ) :
    |deriv (uo z) t| ≤ (|z.re| + |z.im|) * cosh (z.im * t) := by
  rw [deriv_uo]
  calc |z.re * ue z t + z.im * ve z t| ≤ |z.re * ue z t| + |z.im * ve z t| := abs_add_le _ _
    _ = |z.re| * |ue z t| + |z.im| * |ve z t| := by rw [abs_mul, abs_mul]
    _ ≤ |z.re| * cosh (z.im * t) + |z.im| * cosh (z.im * t) :=
        add_le_add (mul_le_mul_of_nonneg_left (abs_ue_le z t) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (abs_ve_le z t) (abs_nonneg _))
    _ = (|z.re| + |z.im|) * cosh (z.im * t) := by ring

/-- `|vo'(t)| ≤ (|x| + |y|) cosh(yt)`. -/
theorem abs_deriv_vo_le (z : ℂ) (t : ℝ) :
    |deriv (vo z) t| ≤ (|z.re| + |z.im|) * cosh (z.im * t) := by
  rw [deriv_vo]
  calc |z.im * ue z t - z.re * ve z t| ≤ |z.im * ue z t| + |z.re * ve z t| := abs_sub _ _
    _ = |z.im| * |ue z t| + |z.re| * |ve z t| := by rw [abs_mul, abs_mul]
    _ ≤ |z.im| * cosh (z.im * t) + |z.re| * cosh (z.im * t) :=
        add_le_add (mul_le_mul_of_nonneg_left (abs_ue_le z t) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (abs_ve_le z t) (abs_nonneg _))
    _ = (|z.re| + |z.im|) * cosh (z.im * t) := by ring

/-! ### The edge constant -/

/-- The edge constant `2 cosh(yL/2) + (|x| + |y|)·2 sinh(|y|L/2)/|y|` of `z = x + iy` on the window of
length `L`. -/
def edgeConst (L : ℝ) (z : ℂ) : ℝ :=
  2 * cosh (z.im * L / 2) + (|z.re| + |z.im|) * (2 * sinh (|z.im| * L / 2) / |z.im|)

/-- For `L ≥ 0`, a continuous `g` with `|g t| ≤ B cosh(yt)` has `∫ |g| ≤ B ∫ cosh(yt)` on the window. -/
theorem integral_abs_le_mul_integral_cosh {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hgc : Continuous g)
    {B y : ℝ} (hg : ∀ t, |g t| ≤ B * cosh (y * t)) :
    ∫ t in -(L / 2)..L / 2, |g t| ≤ B * ∫ t in -(L / 2)..L / 2, cosh (y * t) := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on (by linarith) (hgc.abs.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => B * cosh (y * t)).intervalIntegrable _ _) fun t _ => hg t

/-- For `L ≥ 0` and every `z`: `2|uo z (L/2)| + ∫ |uo'| ≤ 2 cosh(yL/2) + (|x| + |y|) ∫ cosh(yt)`. -/
theorem edge_uo_le_integral {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    2 * |uo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (uo z) t|
      ≤ 2 * cosh (z.im * L / 2)
        + (|z.re| + |z.im|) * ∫ t in -(L / 2)..L / 2, cosh (z.im * t) := by
  have h1 : |uo z (L / 2)| ≤ cosh (z.im * L / 2) := by
    rw [mul_div_assoc]
    exact abs_uo_le z (L / 2)
  have h2 := integral_abs_le_mul_integral_cosh hL (by rw [deriv_uo]; fun_prop) (abs_deriv_uo_le z)
  linarith

/-- For `L ≥ 0` and every `z`: `2|vo z (L/2)| + ∫ |vo'| ≤ 2 cosh(yL/2) + (|x| + |y|) ∫ cosh(yt)`. -/
theorem edge_vo_le_integral {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    2 * |vo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (vo z) t|
      ≤ 2 * cosh (z.im * L / 2)
        + (|z.re| + |z.im|) * ∫ t in -(L / 2)..L / 2, cosh (z.im * t) := by
  have h1 : |vo z (L / 2)| ≤ cosh (z.im * L / 2) := by
    rw [mul_div_assoc]
    exact abs_vo_le z (L / 2)
  have h2 := integral_abs_le_mul_integral_cosh hL (by rw [deriv_vo]; fun_prop) (abs_deriv_vo_le z)
  linarith

/-- **The edge bound for `uo`**: for `L ≥ 0` and `y ≠ 0`, `2|uo z (L/2)| + ∫ |uo'| ≤ edgeConst L z`. -/
theorem edge_uo_le {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hy : z.im ≠ 0) :
    2 * |uo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (uo z) t| ≤ edgeConst L z := by
  rw [edgeConst, ← integral_cosh_mul_eq L hy]
  exact edge_uo_le_integral hL z

/-- **The edge bound for `vo`**: for `L ≥ 0` and `y ≠ 0`, `2|vo z (L/2)| + ∫ |vo'| ≤ edgeConst L z`. -/
theorem edge_vo_le {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hy : z.im ≠ 0) :
    2 * |vo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (vo z) t| ≤ edgeConst L z := by
  rw [edgeConst, ← integral_cosh_mul_eq L hy]
  exact edge_vo_le_integral hL z

/-- The edge constant is nonnegative for `L ≥ 0`. -/
theorem edgeConst_nonneg {L : ℝ} (hL : 0 ≤ L) (z : ℂ) : 0 ≤ edgeConst L z := by
  have hs : 0 ≤ sinh (|z.im| * L / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  unfold edgeConst
  exact add_nonneg (mul_nonneg zero_le_two (Real.cosh_pos _).le)
    (mul_nonneg (by positivity) (div_nonneg (mul_nonneg zero_le_two hs) (abs_nonneg _)))

/-! ### The Bessel defects of `uo` and `vo` -/

/-- **The Bessel defect of an odd `C¹` function**: for `L ≥ 0`,
`projDefect L N h ≤ (2|h(L/2)| + ∫ |h'|)² L/(π²(N+1))`. -/
theorem projDefect_le_of_odd {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {h h' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt h (h' t) t) (hc' : Continuous h') (hodd : ∀ t, h (-t) = -h t) :
    projDefect L N h
      ≤ (2 * |h (L / 2)| + ∫ t in -(L / 2)..L / 2, |h' t|) ^ 2 * L / (π ^ 2 * (N + 1)) := by
  rcases hL.eq_or_lt with rfl | hL
  · simp [projDefect]
  rw [Cvs.StepA.SineModeOddTrial.projDefect_eq_sub_sum]
  exact Cvs.StepA.SineParseval.integral_sq_sub_sum_le hL hd hc' hodd N

/-- **The Bessel defect of `uo z`**: for `L ≥ 0` and `y ≠ 0`,
`projDefect L N (uo z) ≤ edgeConst² L/(π²(N+1))`. -/
theorem projDefect_uo_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hy : z.im ≠ 0) :
    projDefect L N (uo z) ≤ edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by
  have hd : ∀ t, HasDerivAt (uo z) (deriv (uo z) t) t := fun t =>
    (hasDerivAt_uo z t).differentiableAt.hasDerivAt
  have hc' : Continuous (deriv (uo z)) := by rw [deriv_uo]; fun_prop
  refine (projDefect_le_of_odd hL N hd hc' (Cvs.StepA.OneZeroParitySectors.uo_neg z)).trans ?_
  have h0 : 0 ≤ 2 * |uo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (uo z) t| :=
    add_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by linarith) fun t _ => abs_nonneg _)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (edge_uo_le hL hy) 2) hL) (by positivity)

/-- **The Bessel defect of `vo z`**: for `L ≥ 0` and `y ≠ 0`,
`projDefect L N (vo z) ≤ edgeConst² L/(π²(N+1))`. -/
theorem projDefect_vo_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hy : z.im ≠ 0) :
    projDefect L N (vo z) ≤ edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by
  have hd : ∀ t, HasDerivAt (vo z) (deriv (vo z) t) t := fun t =>
    (hasDerivAt_vo z t).differentiableAt.hasDerivAt
  have hc' : Continuous (deriv (vo z)) := by rw [deriv_vo]; fun_prop
  refine (projDefect_le_of_odd hL N hd hc' (Cvs.StepA.OneZeroParitySectors.vo_neg z)).trans ?_
  have h0 : 0 ≤ 2 * |vo z (L / 2)| + ∫ t in -(L / 2)..L / 2, |deriv (vo z) t| :=
    add_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by linarith) fun t _ => abs_nonneg _)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (edge_vo_le hL hy) 2) hL) (by positivity)

/-! ### The traces -/

/-- For `L ≥ 0`, the even and odd traces add up to at most `L cosh(yL)`. -/
theorem sigE_add_sigO_le {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    sigE L z + sigO L z ≤ L * cosh (z.im * L) := by
  rw [Cvs.StepA.OffLineZeroTrade.sigE_add_sigO]
  have hpt : ∀ t ∈ Set.Icc (-(L / 2)) (L / 2), cosh (2 * z.im * t) ≤ cosh (z.im * L) := by
    intro t ht
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hL]
    have : |t| ≤ L / 2 := abs_le.mpr ⟨ht.1, ht.2⟩
    nlinarith [abs_nonneg z.im]
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    ((by fun_prop : Continuous fun t => cosh (2 * z.im * t)).intervalIntegrable _ _)
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- For `L ≥ 0` and `y ≠ 0`, `sigO L z ≤ e^{|y|L}/(2|y|)`. -/
theorem sigO_le_exp {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hy : z.im ≠ 0) :
    sigO L z ≤ exp (|z.im| * L) / (2 * |z.im|) := by
  have hE : 0 ≤ sigE L z := add_nonneg (integral_sq_nonneg hL _) (integral_sq_nonneg hL _)
  have h := Cvs.StepA.OffLineZeroTrade.sigE_add_sigO L z
  rw [integral_cosh_two_mul_eq L hy] at h
  calc sigO L z ≤ sinh (|z.im| * L) / |z.im| := by linarith
    _ ≤ exp (|z.im| * L) / 2 / |z.im| :=
        div_le_div_of_nonneg_right (by linarith [two_mul_sinh_le_exp (|z.im| * L)]) (abs_nonneg _)
    _ = exp (|z.im| * L) / (2 * |z.im|) := by rw [div_div]

/-! ### The projection budget at one scale -/

/-- **The projection budget, exactly in the edge constant**: for `L ≥ 0` and `y ≠ 0`, with
`T = 2·edgeConst² L/(π²(N+1))`, `trialBound L N z − lamO L z ≤ 2√(sigO·T) + T`. -/
theorem trialBound_sub_lamO_le_edgeConst {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hy : z.im ≠ 0) :
    trialBound L N z - lamO L z
      ≤ 2 * √(sigO L z * (2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1))))
        + 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by
  have h1 := projDefect_uo_le hL N hy
  have h2 := projDefect_vo_le hL N hy
  have hτ : projDefect L N (uo z) + projDefect L N (vo z)
      ≤ 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by
    have e : 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1))
        = edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) + edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by
      ring
    linarith
  have hs : 0 ≤ sigO L z := add_nonneg (integral_sq_nonneg hL _) (integral_sq_nonneg hL _)
  have hsq : √(sigO L z * (projDefect L N (uo z) + projDefect L N (vo z)))
      ≤ √(sigO L z * (2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)))) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hτ hs)
  unfold trialBound
  linarith

/-- The edge rate `2 + (|x| + |y|)/|y|` of `z = x + iy`. -/
def edgeRate (z : ℂ) : ℝ := 2 + (|z.re| + |z.im|) / |z.im|

/-- The edge rate is nonnegative. -/
theorem edgeRate_nonneg (z : ℂ) : 0 ≤ edgeRate z := by
  unfold edgeRate
  positivity

/-- For `L ≥ 0`, `edgeConst L z ≤ edgeRate z · e^{|y|L/2}`. -/
theorem edgeConst_le {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    edgeConst L z ≤ edgeRate z * exp (|z.im| * L / 2) := by
  have h1 : cosh (z.im * L / 2) ≤ exp (|z.im| * L / 2) := by
    refine (cosh_le_exp_abs _).trans_eq ?_
    rw [abs_div, abs_mul, abs_of_nonneg hL, abs_two]
  have h2 := mul_le_mul_of_nonneg_left (two_mul_sinh_le_exp (|z.im| * L / 2))
    (by positivity : 0 ≤ (|z.re| + |z.im|) / |z.im|)
  have e : (|z.re| + |z.im|) * (2 * sinh (|z.im| * L / 2) / |z.im|)
      = (|z.re| + |z.im|) / |z.im| * (2 * sinh (|z.im| * L / 2)) := by ring
  unfold edgeConst edgeRate
  rw [e]
  linarith

/-- The projection envelope `2·edgeRate·√(r/|y|)/π + 2·edgeRate²·r/π²` at the ratio `r`. -/
def projEnv (z : ℂ) (r : ℝ) : ℝ :=
  2 * edgeRate z * √(r / |z.im|) / π + 2 * edgeRate z ^ 2 * r / π ^ 2

/-- The projection envelope is continuous in the ratio. -/
theorem continuous_projEnv (z : ℂ) : Continuous (projEnv z) := by
  unfold projEnv
  fun_prop

/-- The projection envelope vanishes at ratio `0`. -/
theorem projEnv_zero (z : ℂ) : projEnv z 0 = 0 := by
  simp [projEnv]

/-- The projection envelope is monotone in the ratio. -/
theorem projEnv_mono (z : ℂ) : Monotone (projEnv z) := by
  intro r s hrs
  have hR := edgeRate_nonneg z
  have h1 : √(r / |z.im|) ≤ √(s / |z.im|) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hrs (abs_nonneg _))
  have h2 : 2 * edgeRate z * √(r / |z.im|) / π ≤ 2 * edgeRate z * √(s / |z.im|) / π :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) pi_pos.le
  have h3 : 2 * edgeRate z ^ 2 * r / π ^ 2 ≤ 2 * edgeRate z ^ 2 * s / π ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrs (by positivity)) (by positivity)
  unfold projEnv
  linarith

/-- **The projection budget against `e^{|y|L}`**: for `L ≥ 0`, every `N` and `y ≠ 0`,
`trialBound L N z − lamO L z ≤ projEnv z (L/(N+1)) · e^{|y|L}`. -/
theorem trialBound_sub_lamO_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hy : z.im ≠ 0) :
    trialBound L N z - lamO L z ≤ projEnv z (L / (N + 1)) * exp (|z.im| * L) := by
  set r := L / ((N : ℝ) + 1) with hr
  set E := exp (|z.im| * L) with hE
  set R := edgeRate z with hRdef
  have hy' : 0 < |z.im| := abs_pos.mpr hy
  have hR : 0 ≤ R := edgeRate_nonneg z
  have hr0 : 0 ≤ r := by positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hc0 := edgeConst_nonneg hL z
  have hhalf : exp (|z.im| * L / 2) ^ 2 = E := by
    rw [sq, ← Real.exp_add, hE]
    congr 1
    ring
  have hsq : edgeConst L z ^ 2 ≤ R ^ 2 * E := by
    calc edgeConst L z ^ 2 ≤ (R * exp (|z.im| * L / 2)) ^ 2 :=
          pow_le_pow_left₀ hc0 (edgeConst_le hL z) 2
      _ = R ^ 2 * E := by rw [mul_pow, hhalf]
  have hTr : 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) = 2 * edgeConst L z ^ 2 * r / π ^ 2 := by
    rw [hr]
    field_simp
  have hT : 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) ≤ 2 * R ^ 2 * r / π ^ 2 * E := by
    rw [hTr]
    have := mul_le_mul_of_nonneg_right hsq hr0
    calc 2 * edgeConst L z ^ 2 * r / π ^ 2 = 2 * (edgeConst L z ^ 2 * r) / π ^ 2 := by ring
      _ ≤ 2 * (R ^ 2 * E * r) / π ^ 2 := by gcongr
      _ = 2 * R ^ 2 * r / π ^ 2 * E := by ring
  have hT0 : 0 ≤ 2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1)) := by positivity
  have hs0 : 0 ≤ sigO L z := add_nonneg (integral_sq_nonneg hL _) (integral_sq_nonneg hL _)
  have hroot : √(sigO L z * (2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1))))
      ≤ R * √(r / |z.im|) / π * E := by
    have hprod := mul_le_mul (sigO_le_exp hL hy) hT hT0 (by positivity)
    have heq : E / (2 * |z.im|) * (2 * R ^ 2 * r / π ^ 2 * E) = (R * E / π) ^ 2 * (r / |z.im|) := by
      field_simp
    calc √(sigO L z * (2 * edgeConst L z ^ 2 * L / (π ^ 2 * (N + 1))))
        ≤ √((R * E / π) ^ 2 * (r / |z.im|)) := Real.sqrt_le_sqrt (hprod.trans heq.le)
      _ = R * E / π * √(r / |z.im|) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      _ = R * √(r / |z.im|) / π * E := by ring
  refine (trialBound_sub_lamO_le_edgeConst hL N hy).trans ?_
  have e : projEnv z r * E = 2 * (R * √(r / |z.im|) / π * E) + 2 * R ^ 2 * r / π ^ 2 * E := by
    unfold projEnv
    ring
  rw [e]
  linarith

/-! ### Asymptotics in `L` -/

/-- **The on-line budget at polynomially many modes**: if `N L = O(L^k)`, then
`onLineBound L (N L) = o(e^{cL})` for every `c > 0`. -/
theorem isLittleO_onLineBound_of_isBigO {N : ℝ → ℕ} {k : ℕ}
    (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L ^ k) {c : ℝ} (hc : 0 < c) :
    (fun L => onLineBound L (N L)) =o[atTop] fun L => exp (c * L) := by
  set S := ∑' ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
    (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2)) with hS
  have h1 : (fun L : ℝ => L) =o[atTop] fun L => exp (c * L) := by
    simpa only [pow_one] using isLittleO_pow_exp_pos_mul_atTop 1 hc
  have h2 : (fun L : ℝ => (N L : ℝ) ^ 2 * L⁻¹) =o[atTop] fun L => exp (c * L) := by
    have h3 : (fun L : ℝ => (N L : ℝ) ^ 2 * L⁻¹) =O[atTop] fun L => (L ^ k) ^ 2 * 1 :=
      (hN.pow 2).mul (tendsto_inv_atTop_zero.isBigO_one ℝ)
    refine h3.trans_isLittleO ?_
    simpa only [mul_one, ← pow_mul] using isLittleO_pow_exp_pos_mul_atTop (k * 2) hc
  refine ((h1.const_mul_left S).add (h2.const_mul_left ((2 * π) ^ 2 * S))).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with L hL
  simp only [onLineBound, ← hS]
  field_simp

/-- For `|y| < c`, `L cosh(yL) = o(e^{cL})`. -/
theorem isLittleO_mul_cosh {y c : ℝ} (h : |y| < c) :
    (fun L => L * cosh (y * L)) =o[atTop] fun L => exp (c * L) := by
  have h1 : (fun L : ℝ => L) =o[atTop] fun L => exp ((c - |y|) * L) := by
    simpa only [pow_one] using isLittleO_pow_exp_pos_mul_atTop 1 (sub_pos.mpr h)
  have h2 : (fun L : ℝ => L * exp (|y| * L)) =o[atTop] fun L => exp (c * L) := by
    refine (h1.mul_isBigO (isBigO_refl (fun L : ℝ => exp (|y| * L)) atTop)).congr_right ?_
    intro L
    rw [← Real.exp_add]
    congr 1
    ring
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) h2
  filter_upwards [eventually_ge_atTop 0] with L hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL (Real.cosh_pos _).le),
    abs_of_nonneg (mul_nonneg hL (Real.exp_pos _).le), one_mul]
  refine mul_le_mul_of_nonneg_left ((cosh_le_exp_abs _).trans_eq ?_) hL
  rw [abs_mul, abs_of_nonneg hL]

/-! ### The projection error at bandwidth `Ω` -/

/-- The projection rate at bandwidth `Ω`: the projection envelope at the ratio `2π/Ω`. -/
def projRate (z : ℂ) (Ω : ℝ) : ℝ := projEnv z (2 * π / Ω)

/-- The projection rate tends to `0` as the bandwidth grows. -/
theorem tendsto_projRate (z : ℂ) : Tendsto (projRate z) atTop (𝓝 0) := by
  have h : Tendsto (fun Ω : ℝ => 2 * π / Ω) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 := ((continuous_projEnv z).tendsto 0).comp h
  rw [projEnv_zero] at h2
  exact h2

/-- At `N = ⌈ΩL/2π⌉₊` with `Ω > 0`, the ratio `L/(N+1)` is at most `2π/Ω`. -/
theorem div_natCeil_add_one_le {L Ω : ℝ} (hΩ : 0 < Ω) :
    L / ((⌈Ω * L / (2 * π)⌉₊ : ℝ) + 1) ≤ 2 * π / Ω := by
  have h1 : Ω * L / (2 * π) ≤ (⌈Ω * L / (2 * π)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at h1
  rw [div_le_div_iff₀ (by positivity) hΩ]
  nlinarith [pi_pos]

/-- **The projection error at bandwidth `Ω`**: for `L ≥ 0`, `y ≠ 0` and `Ω > 0`,
`trialBound L ⌈ΩL/2π⌉₊ z − lamO L z ≤ projRate z Ω · e^{|y|L}`. -/
theorem trialBound_sub_lamO_le_projRate {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hy : z.im ≠ 0) {Ω : ℝ}
    (hΩ : 0 < Ω) :
    trialBound L ⌈Ω * L / (2 * π)⌉₊ z - lamO L z ≤ projRate z Ω * exp (|z.im| * L) :=
  (trialBound_sub_lamO_le hL _ hy).trans
    (mul_le_mul_of_nonneg_right (projEnv_mono z (div_natCeil_add_one_le hΩ)) (Real.exp_pos _).le)

end Cvs.StepA.OddTrialErrorBudget
