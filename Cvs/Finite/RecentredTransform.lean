import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.DiscreteSpine
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
# The transform, recentred on the window's midpoint

A window placed on `(0, L]` carries its midpoint in the exponent, so its transform is the
transform about the midpoint times a phase of unit modulus. The phase never vanishes and is
entire, so it changes neither differentiability nor zero-freeness off the axes, and the spine runs
on the recentred transforms exactly as it runs on the placed ones.
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace Cvs.Finite.RecentredTransform
open Cvs.ZeroCounting

/-- The phase carried by a window placed at `(0, L]` rather than about its midpoint. -/
def phase (L : ℝ) : ℂ → ℂ := fun z => Complex.exp (-(Complex.I * z * (L : ℂ) / 2))

theorem phase_ne_zero (L : ℝ) (z : ℂ) : phase L z ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_phase (L : ℝ) : Differentiable ℂ (phase L) := by
  unfold phase
  exact Complex.differentiable_exp.comp (by fun_prop)

/-- **Shifting the window shifts the transform by a phase.** -/
theorem fourierLaplace_shift (g : ℝ → ℂ) (a : ℝ) (z : ℂ) :
    FourierLaplace.fourierLaplace g z
      = Complex.exp (Complex.I * z * (a : ℂ))
        * ∫ s : ℝ, g (a + s) * Complex.exp (Complex.I * z * (s : ℂ)) := by
  rw [FourierLaplace.fourierLaplace,
    ← integral_add_left_eq_self a
      (f := fun t : ℝ => g t * Complex.exp (Complex.I * z * (t : ℂ))),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  have hexp : Complex.I * z * ((a + s : ℝ) : ℂ)
      = Complex.I * z * (a : ℂ) + Complex.I * z * (s : ℂ) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  ring

/-- The ground state's transform, recentred on the window's midpoint. -/
def cgtransform (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) : ℂ → ℂ :=
  fun z => phase L z * Cvs.Limit.SpineWithoutSimplicity.gtransform P R hL N z

theorem differentiable_cgtransform (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Differentiable ℂ (cgtransform P R hL N) :=
  (differentiable_phase L).mul (Cvs.Limit.DiscreteSpine.differentiable_modeSum hL _ _)

/-- **Recentring keeps the transform zero-free off the axes**, the phase never vanishing. -/
theorem cgtransform_ne_zero (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ)
    {z : ℂ} (hz : z ∈ Cvs.Limit.OffAxesLimit.offAxes) : cgtransform P R hL N z ≠ 0 :=
  mul_ne_zero (phase_ne_zero L z)
    ((Cvs.Limit.SpineWithoutSimplicity.ground_spec P R hL N).2.2.2.2 z hz)

end Cvs.Finite.RecentredTransform
