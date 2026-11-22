import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineNormalised
import Cvs.Limit.ZeroFreeApproximantsRH

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis spine with its constants chosen rather than assumed

Taking the rescaling constant to be the inverse modulus of the recentred transform at the point
makes it real and pins the modulus at one, so the spine of `Cvs.Limit.OffAxisSpineNormalised` runs with no hypothesis about
the constants at all, leaving the convergence and the zeros the limit must see.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.OffAxisSpineChosenConstants
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- The rescaling that puts the recentred transform on the unit circle at `w₀`. -/
def cnorm (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) (w₀ : ℂ) : ℂ :=
  ((‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖⁻¹ : ℝ) : ℂ)

/-- The rescaling is real, being the cast of a real number. -/
theorem cnorm_im (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) (w₀ : ℂ) :
    (cnorm P R hL N w₀).im = 0 := Complex.ofReal_im _

/-- **The rescaling puts the approximant on the unit circle at a point off the axes.** -/
theorem norm_cnorm_mul (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {w₀ : ℂ}
    (hw₀ : w₀ ∈ offAxes) :
    ‖cnorm P R hL N w₀ * Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖ = 1 := by
  have hn : ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Cvs.Finite.RecentredTransform.cgtransform_ne_zero P R hL N hw₀)
  rw [norm_mul, cnorm, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

/-- **The off-axis spine with the constants chosen**, leaving the convergence and the zeros seen. -/
theorem riemannHypothesis_of_ground_centred_offAxes_conv
    {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (f : ℂ → ℂ) {w₀ : ℂ}
    (hw₀ : w₀ ∈ offAxes)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => cnorm (P n) (R n) (hL n) (N n) w₀
        * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      f atTop offAxes)
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis :=
  Cvs.Limit.OffAxisSpineNormalised.riemannHypothesis_of_ground_centred_offAxes_real_normalised
    hL P R N (fun n => cnorm (P n) (R n) (hL n) (N n) w₀) f hw₀
    (fun n => cnorm_im (P n) (R n) (hL n) (N n) w₀)
    (fun n => norm_cnorm_mul (P n) (R n) (hL n) (N n) hw₀)
    hconv hsees

end Cvs.Limit.OffAxisSpineChosenConstants
