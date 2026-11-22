import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SecularRealRooted
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
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
# The recentred transform, in closed form

Recentring cancels the half-turn the placed window carries: the universal factor `i z (e^{izL}-1)`
becomes `-2 z sin(zL/2)`, which is real wherever the frequency is. So the recentred transform is a
real multiple of the rational factor on the real axis, and its only zeros there beyond those of the
rational factor are the lattice points.
-/

noncomputable section

open Real

namespace Cvs.Finite.RecentredTransformClosed
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- The exponential form of the sine. -/
theorem exp_sub_exp_neg (w : ℂ) :
    Complex.exp (Complex.I * w) - Complex.exp (-(Complex.I * w))
      = 2 * Complex.sin w * Complex.I := by
  have h1 : Complex.exp (Complex.I * w) = Complex.cos w + Complex.sin w * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I w
  have h2 : Complex.exp (-(Complex.I * w)) = Complex.cos w - Complex.sin w * Complex.I := by
    have hrw : -(Complex.I * w) = (-w) * Complex.I := by ring
    rw [hrw, Complex.exp_mul_I (-w), Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  ring

/-- **Recentring turns the universal factor into a sine.** -/
theorem phase_mul_universal (z : ℂ) (L : ℝ) :
    Complex.exp (-(Complex.I * z * (L : ℂ) / 2))
        * (Complex.I * z * (Complex.exp (Complex.I * z * (L : ℂ)) - 1))
      = -2 * z * Complex.sin (z * (L : ℂ) / 2) := by
  set w : ℂ := z * (L : ℂ) / 2 with hw
  have h2w : Complex.I * z * (L : ℂ) = 2 * (Complex.I * w) := by rw [hw]; ring
  have hneg : -(Complex.I * z * (L : ℂ) / 2) = -(Complex.I * w) := by rw [hw]; ring
  rw [hneg, h2w]
  have key : Complex.exp (-(Complex.I * w)) * Complex.exp (2 * (Complex.I * w))
      = Complex.exp (Complex.I * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  calc Complex.exp (-(Complex.I * w))
        * (Complex.I * z * (Complex.exp (2 * (Complex.I * w)) - 1))
      = Complex.I * z * (Complex.exp (-(Complex.I * w)) * Complex.exp (2 * (Complex.I * w))
          - Complex.exp (-(Complex.I * w))) := by ring
    _ = Complex.I * z * (Complex.exp (Complex.I * w) - Complex.exp (-(Complex.I * w))) := by
        rw [key]
    _ = Complex.I * z * (2 * Complex.sin w * Complex.I) := by rw [exp_sub_exp_neg]
    _ = -2 * z * Complex.sin w := by linear_combination (2 * z * Complex.sin w) * hI

/-- **The recentred transform in closed form**, with the phase gone. -/
theorem centred_fourierLaplace_eq_sin {L : ℝ} (hL : 0 < L)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) {z : ℂ}
    (hz : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0) :
    Complex.exp (-(Complex.I * z * (L : ℂ) / 2))
        * FourierLaplace.fourierLaplace
            (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)) z
      = -2 * z * Complex.sin (z * (L : ℂ) / 2) * Cvs.Finite.UniversalFunctionPairing.S L mode xi z := by
  rw [Cvs.Finite.SecularRealRooted.fourierLaplace_eq_S hL hinv hmode hxieven hz, ← mul_assoc,
    phase_mul_universal z L]

/-- **The recentred ground-state transform, in closed form.** -/
theorem cgtransform_eq_sin (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ}
    (hz : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) i : ℝ) : ℂ)
      + z ≠ 0) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N z
      = -2 * z * Complex.sin (z * (L : ℂ) / 2)
        * Cvs.Finite.UniversalFunctionPairing.S L (Cvs.Finite.SymmetricModeSet.mode N)
            (Cvs.Limit.SpineWithoutSimplicity.ground P R L hL N) z := by
  unfold Cvs.Finite.RecentredTransform.cgtransform Cvs.Finite.RecentredTransform.phase
    Cvs.Limit.SpineWithoutSimplicity.gtransform
  exact centred_fourierLaplace_eq_sin hL (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) ((Cvs.Limit.SpineWithoutSimplicity.ground_spec P R hL N).1) hz

end Cvs.Finite.RecentredTransformClosed
