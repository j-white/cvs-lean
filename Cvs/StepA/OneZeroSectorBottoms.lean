import Mathlib
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.RankTwoBottom

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One zero's sector bottoms on the window and their exact splitting
On even (odd) continuous profiles, `Re sqTransform(z)/∫ f²` has minimum `lamE` (`lamO`), the `lamMinus` of
the sector Gram data, for every `L > 0` and every `z`. Exactly, with `ρ` the ratio of the trace sum
to the sum of the two discriminant roots, `2(lamO − lamE) = ρ·L sinc(xL) − ∫ cos 2xt cosh 2yt`, and
`4|z|(lamO − lamE) = 2|z|ρ L sinc(xL) − e^{−yL} sin(xL − arg z) − e^{yL} sin(xL + arg z)`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.OneZeroSectorBottoms
open Cvs.ZeroCounting

open Cvs.StepA.OneZeroParitySectors (ue ve uo vo continuous_ue continuous_ve continuous_uo continuous_vo winForm winForm_apply winForm_isSymm winForm_self_nonneg winForm_sq ve_eq_zero vo_eq_zero uo_eq_zero)
open Cvs.StepA.RankTwoBottom (lamMinus)

/-! ### The window pairing on continuous profiles -/

/-- A profile nonzero somewhere inside the window has positive square integral. -/
theorem winForm_self_pos {L : ℝ} (hL : 0 < L) (f : C(ℝ, ℝ)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (-(L / 2)) (L / 2)) (hf : f t₀ ≠ 0) : 0 < winForm L f f :=
  intervalIntegral.integral_pos (by linarith) (f.continuous.mul f.continuous).continuousOn
    (fun t _ => mul_self_nonneg _) ⟨t₀, Ioo_subset_Icc_self ht₀, mul_self_pos.mpr hf⟩

/-- A continuous function nonzero somewhere inside the window has positive square integral. -/
theorem integral_sq_pos {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (-(L / 2)) (L / 2)) (hf0 : f t₀ ≠ 0) : 0 < ∫ t in -(L / 2)..L / 2, f t ^ 2 := by
  have h := winForm_self_pos hL ⟨f, hf⟩ ht₀ hf0
  rwa [winForm_sq] at h

/-- **Cauchy–Schwarz for the window pairing, at every `L`.** -/
theorem winForm_sq_le (L : ℝ) (f g : C(ℝ, ℝ)) :
    winForm L f g ^ 2 ≤ winForm L f f * winForm L g g := by
  rcases le_or_gt 0 L with hL | hL
  · exact LinearMap.BilinForm.apply_sq_le_of_symm _ (winForm_self_nonneg hL)
      (LinearMap.BilinForm.isSymm_iff.mp (winForm_isSymm L)) f g
  · have hneg : ∀ f g : C(ℝ, ℝ), winForm (-L) f g = -winForm L f g := fun f g => by
      rw [winForm_apply, winForm_apply, show -(-L / 2) = L / 2 by ring, show -L / 2 = -(L / 2) by ring,
        intervalIntegral.integral_symm]
    have h := LinearMap.BilinForm.apply_sq_le_of_symm _ (winForm_self_nonneg (L := -L) (by linarith))
      (LinearMap.BilinForm.isSymm_iff.mp (winForm_isSymm (-L))) f g
    rw [hneg, hneg, hneg] at h
    linarith

/-! ### The sector weights are independent on the window -/

/-- `uo' = x ue + y ve`. -/
theorem hasDerivAt_uo (z : ℂ) (t : ℝ) : HasDerivAt (uo z) (z.re * ue z t + z.im * ve z t) t := by
  have h1 : HasDerivAt (fun y => sin (z.re * y)) (cos (z.re * t) * z.re) t := by
    simpa using ((hasDerivAt_id t).const_mul z.re).sin
  have h2 : HasDerivAt (fun y => cosh (z.im * y)) (sinh (z.im * t) * z.im) t := by
    simpa using ((hasDerivAt_id t).const_mul z.im).cosh
  exact (h1.mul h2).congr_deriv (by unfold ue ve; ring)

/-- `vo' = y ue − x ve`. -/
theorem hasDerivAt_vo (z : ℂ) (t : ℝ) : HasDerivAt (vo z) (z.im * ue z t - z.re * ve z t) t := by
  have h1 : HasDerivAt (fun y => cos (z.re * y)) (-sin (z.re * t) * z.re) t := by
    simpa using ((hasDerivAt_id t).const_mul z.re).cos
  have h2 : HasDerivAt (fun y => sinh (z.im * y)) (cosh (z.im * t) * z.im) t := by
    simpa using ((hasDerivAt_id t).const_mul z.im).sinh
  exact (h1.mul h2).congr_deriv (by unfold ue ve; ring)

/-! ### The sector bottoms -/

/-- The even-sector bottom of one zero's term: `lamMinus` of `(∫ ue², ∫ ve², ∫ ue ve)`. -/
def lamE (L : ℝ) (z : ℂ) : ℝ :=
  lamMinus (∫ t in -(L / 2)..L / 2, ue z t ^ 2) (∫ t in -(L / 2)..L / 2, ve z t ^ 2)
    (∫ t in -(L / 2)..L / 2, ue z t * ve z t)

/-- The odd-sector bottom of one zero's term: `lamMinus` of `(∫ uo², ∫ vo², ∫ uo vo)`. -/
def lamO (L : ℝ) (z : ℂ) : ℝ :=
  lamMinus (∫ t in -(L / 2)..L / 2, uo z t ^ 2) (∫ t in -(L / 2)..L / 2, vo z t ^ 2)
    (∫ t in -(L / 2)..L / 2, uo z t * vo z t)

/-! ### The exact splitting -/

/-- The even trace `∫ ue² + ∫ ve²`. -/
def sigE (L : ℝ) (z : ℂ) : ℝ :=
  (∫ t in -(L / 2)..L / 2, ue z t ^ 2) + ∫ t in -(L / 2)..L / 2, ve z t ^ 2

/-- The odd trace `∫ uo² + ∫ vo²`. -/
def sigO (L : ℝ) (z : ℂ) : ℝ :=
  (∫ t in -(L / 2)..L / 2, uo z t ^ 2) + ∫ t in -(L / 2)..L / 2, vo z t ^ 2

end Cvs.StepA.OneZeroSectorBottoms
