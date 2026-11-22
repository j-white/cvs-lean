import Mathlib
import Cvs.Finite.BracketMomentsClosed
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole channel of every pair value, in closed form

The pole pairing is the integral of `2cosh(x/2)` against the kernel over the window alone, and the
kernel's cosine, sine and linear-cosine pieces have elementary antiderivatives at the rates `±1/2`;
at a lattice frequency the trigonometric factors return to their values at the origin, so every
pole pairing is a rational function of the frequencies times `exp(L/2) + exp(-L/2) - 2`.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.PairPoleChannelClosed

open Cvs.Finite.CosineModeOverlap Cvs.Finite.LevyKernelIncrement Cvs.Finite.BracketMomentsClosed

/-- The lattice frequency `2πm/L` of mode `m`. -/
def freq (L : ℝ) (m : ℤ) : ℝ := 2 * π * m / L

/-- The exponential factor `exp(L/2) + exp(-L/2) - 2` shared by every pole pairing. -/
def poleFactor (L : ℝ) : ℝ := Real.exp (L / 2) + Real.exp (-(L / 2)) - 2

theorem cos_freq_mul {L : ℝ} (hL : L ≠ 0) (m : ℤ) : Real.cos (freq L m * L) = 1 := by
  rw [show freq L m * L = (m : ℝ) * (2 * π) by unfold freq; field_simp]
  exact Real.cos_int_mul_two_pi m

theorem sin_freq_mul {L : ℝ} (hL : L ≠ 0) (m : ℤ) : Real.sin (freq L m * L) = 0 := by
  rw [show freq L m * L = ((2 * m : ℤ) : ℝ) * π by unfold freq; push_cast; field_simp]
  exact Real.sin_int_mul_pi _

/-- **The pole pairing lives on the window.** -/
theorem polePair_eq_interval {L : ℝ} (hL : 0 < L) (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.polePair L m n
      = ∫ x in (0:ℝ)..L, (Real.exp (-(x / 2)) + Real.exp (x / 2)) * K L m n x := by
  unfold Cvs.Finite.ModeSumPairValues.polePair
  rw [← Ioc_union_Ioi_eq_Ioi hL.le]
  have hdisj : Disjoint (Ioc (0:ℝ) L) (Ioi L) := by
    rw [Set.disjoint_left]; intro u hu hu'; exact absurd hu.2 (not_le.mpr hu')
  have hf1 : ∀ x ∈ Ioc (0:ℝ) L,
      (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Kc L m n x
        = (Real.exp (-(x / 2)) + Real.exp (x / 2)) * K L m n x := by
    intro x hx; rw [Kc_of_le hx.2]
  have hf2 : ∀ x ∈ Ioi L, (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Kc L m n x = 0 := by
    intro x hx
    have : L < x := hx
    rw [Kc_of_gt this, mul_zero]
  have hi1 : IntegrableOn (fun x : ℝ => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Kc L m n x)
      (Ioc 0 L) volume := by
    refine IntegrableOn.congr_fun ?_ (fun x hx => (hf1 x hx).symm) measurableSet_Ioc
    exact ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(x / 2)) + Real.exp (x / 2)).mul
      (continuous_K L m n)).integrableOn_Ioc
  have hi2 : IntegrableOn (fun x : ℝ => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Kc L m n x)
      (Ioi L) volume := by
    refine IntegrableOn.congr_fun ?_ (fun x hx => (hf2 x hx).symm) measurableSet_Ioi
    exact integrableOn_zero
  rw [setIntegral_union hdisj measurableSet_Ioi hi1 hi2,
    setIntegral_congr_fun measurableSet_Ioc hf1, setIntegral_congr_fun measurableSet_Ioi hf2,
    ← intervalIntegral.integral_of_le hL.le]
  simp

/-! ### The diagonal -/

/-- The antiderivative of `2cosh(x/2)·2(1 − x/L)cos(bx)`. -/
def diagAnti (L b : ℝ) : ℝ → ℝ := fun u =>
  2 * (expCos (1 / 2) b u - 1 / L * uExpCos (1 / 2) b u + expCos (-(1 / 2)) b u
    - 1 / L * uExpCos (-(1 / 2)) b u)

theorem hasDerivAt_diagAnti (L : ℝ) (m : ℤ) (x : ℝ) :
    HasDerivAt (diagAnti L (freq L m)) ((Real.exp (-(x / 2)) + Real.exp (x / 2)) * K L m m x) x := by
  have h1 : (1 / 2 : ℝ) ^ 2 + freq L m ^ 2 ≠ 0 := by positivity
  have h2 : (-(1 / 2) : ℝ) ^ 2 + freq L m ^ 2 ≠ 0 := by positivity
  have hd := ((((hasDerivAt_expCos h1 x).sub ((hasDerivAt_uExpCos h1 x).const_mul (1 / L))).add
    (hasDerivAt_expCos h2 x)).sub ((hasDerivAt_uExpCos h2 x).const_mul (1 / L))).const_mul 2
  refine hd.congr_deriv ?_
  have e1 : Real.exp (-(1 / 2 * x)) = Real.exp (-(x / 2)) := by congr 1; ring
  have e2 : Real.exp (-(-(1 / 2) * x)) = Real.exp (x / 2) := by congr 1; ring
  have e3 : Real.cos (freq L m * x) = Real.cos (2 * π * m * x / L) := by
    congr 1; unfold freq; ring
  simp only [K, if_true, e1, e2, e3]
  ring

/-- **The diagonal pole pairing**, in closed form. -/
theorem polePair_diag {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.ModeSumPairValues.polePair L m m
      = 2 / L * (1 / 4 - freq L m ^ 2) * poleFactor L / (1 / 4 + freq L m ^ 2) ^ 2 := by
  rw [polePair_eq_interval hL, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_diagAnti L m x)
    (((by fun_prop : Continuous fun x : ℝ => Real.exp (-(x / 2)) + Real.exp (x / 2)).mul
      (continuous_K L m m)).intervalIntegrable 0 L)]
  have hc := cos_freq_mul hL.ne' m
  have hs := sin_freq_mul hL.ne' m
  simp only [diagAnti, expCos, uExpCos, hc, hs, mul_zero, mul_one, zero_mul, sub_zero, add_zero,
    Real.cos_zero, Real.sin_zero, neg_zero, Real.exp_zero]
  have e1 : Real.exp (-(1 / 2 * L)) = Real.exp (-(L / 2)) := by congr 1; ring
  have e2 : Real.exp (-(-(1 / 2) * L)) = Real.exp (L / 2) := by congr 1; ring
  rw [e1, e2]
  unfold poleFactor
  have hD : (1 / 4 : ℝ) + freq L m ^ 2 ≠ 0 := by positivity
  have h1 : (1 / 2 : ℝ) ^ 2 + freq L m ^ 2 ≠ 0 := by positivity
  have h2 : (-(1 / 2) : ℝ) ^ 2 + freq L m ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Off the diagonal -/

end Cvs.Finite.PairPoleChannelClosed
