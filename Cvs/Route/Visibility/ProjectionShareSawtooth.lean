import Mathlib
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Projection share, the sawtooth transform, and the window transform at a zero

A pairing bound `|⟪r, b⟫| ≤ K‖r‖` on `R` gives `‖P_R b‖ ≤ K`. By parts against `P(v) = {v}(1 − {v})/2`,
`‖x^ρ ∫_x^∞ (1/2 − {v}) v^{−ρ−1} dv‖ ≤ ‖ρ + 1‖/(8(1 + Re ρ)x)`. For `G` `C¹` with mean zero the exterior E-image is in
`L²(1, ∞)`, so an earlier result holds unconditionally; at `1 − ρ` the E-image splits as `(a/θ)(G(1)S(θ/a) − G(0)/2) + r_G`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)

namespace Cvs.Route.Visibility.ProjectionShareSawtooth

/-! ### The projection share from a pairing bound -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R : Submodule ℝ E)
  [R.HasOrthogonalProjection]

/-- `‖P_R b‖² = ⟪P_R b, b⟫`. -/
theorem norm_starProjection_sq_eq_inner (b : E) :
    ‖R.starProjection b‖ ^ 2 = inner ℝ (R.starProjection b) b := by
  have h0 : inner ℝ (b - R.starProjection b) (R.starProjection b) = 0 :=
    R.starProjection_inner_eq_zero b _ (R.starProjection_apply_mem b)
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at h0
  linarith

/-- A pairing bound `|⟪r, b⟫| ≤ K‖r‖` on `R` gives `‖P_R b‖² ≤ K‖P_R b‖`. -/
theorem norm_starProjection_sq_le_of_pairing {b : E} {K : ℝ} (h : ∀ r ∈ R, |inner ℝ r b| ≤ K * ‖r‖) :
    ‖R.starProjection b‖ ^ 2 ≤ K * ‖R.starProjection b‖ := by
  rw [norm_starProjection_sq_eq_inner]
  exact (le_abs_self _).trans (h _ (R.starProjection_apply_mem b))

/-- A pairing bound `|⟪r, b⟫| ≤ K‖r‖` on `R`, `K ≥ 0`, gives `‖P_R b‖ ≤ K`. -/
theorem norm_starProjection_le_of_pairing {b : E} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ r ∈ R, |inner ℝ r b| ≤ K * ‖r‖) : ‖R.starProjection b‖ ≤ K := by
  have hs := norm_starProjection_sq_le_of_pairing R h
  rcases (norm_nonneg (R.starProjection b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact hK
  · rw [sq] at hs; exact le_of_mul_le_mul_right hs h0

end Projection

/-! ### The sawtooth and its periodic antiderivative -/

/-- The sawtooth `S(y) = 1/2 − {y}`. -/
def saw (y : ℝ) : ℝ := 1 / 2 - Int.fract y

theorem abs_saw_le (y : ℝ) : |saw y| ≤ 1 / 2 := by
  unfold saw; rw [abs_le]; constructor <;> linarith [Int.fract_nonneg y, Int.fract_lt_one y]

theorem measurable_saw : Measurable saw := measurable_const.sub measurable_fract

/-! ### The sawtooth transform by parts -/

section Sawtooth

variable {ρ : ℂ}

theorem hasDerivAt_ofReal_cpow {v : ℝ} (hv : 0 < v) (c : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ c) (c * (v : ℂ) ^ (c - 1)) v := by
  have h := ((hasDerivAt_id (v : ℂ)).cpow_const (c := c)
    (Complex.ofReal_mem_slitPlane.2 hv)).comp_ofReal
  simpa using h

end Sawtooth

/-! ### Exterior regularity and the exterior bound without side hypotheses -/

/-! ### The reflected half -/

section ReflectedPsi

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
  (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c)
include hg hg₁ hg₂c hc

end ReflectedPsi

/-- The reflected remainder `r_G(θ) = E_G(θ) − (a/θ)(G(1)S(θ/a) − G(0)/2)`. -/
def reflRem (a : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  eimage a G θ - a / θ * (G 1 * saw (θ / a) - G 0 / 2)

theorem eimage_eq_saw_add_reflRem (a : ℝ) (G : ℝ → ℝ) (θ : ℝ) :
    eimage a G θ = a / θ * (G 1 * saw (θ / a) - G 0 / 2) + reflRem a G θ := by
  unfold reflRem; ring

theorem measurable_reflRem {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) :
    Measurable (reflRem a G) := by
  unfold reflRem
  exact (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).sub
    ((measurable_const.div measurable_id).mul
      ((measurable_const.mul (measurable_saw.comp (measurable_id.div_const a))).sub measurable_const))

end Cvs.Route.Visibility.ProjectionShareSawtooth
