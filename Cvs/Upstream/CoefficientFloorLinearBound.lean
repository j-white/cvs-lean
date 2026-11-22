import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.EvenFirstCellProfile
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Coefficient floors bound linear maps by a quadratic form

Let `F` be degree-2 homogeneous on `ι → ℝ` with `δ j ≤ F b` whenever `b j = 1`. Scaling gives
`b j² δ j ≤ F b`, so `|b j| ≤ √(F b)/√(δ j)`, and any linear `T` obeys
`‖T b‖ ≤ (Σ_j ‖T e_j‖/√(δ j)) √(F b)`. With `F` the even first-cell energy of Cvs.Route.Visibility.EvenFirstCellProfile this bounds `‖T b‖` by the norm
of the even part of the spine class.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Upstream.CoefficientFloorLinearBound
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (eimage)

section General

variable {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ} {δ : ι → ℝ}

/-- A floor on the unit-coefficient slices bounds each squared coefficient: `b j² δ j ≤ F b`. -/
theorem coef_sq_mul_le (hF : ∀ (t : ℝ) (b : ι → ℝ), F (t • b) = t ^ 2 * F b)
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ : ∀ j (b : ι → ℝ), b j = 1 → δ j ≤ F b) (b : ι → ℝ) (j : ι) :
    b j ^ 2 * δ j ≤ F b := by
  have scaled : ∀ k, b k ≠ 0 → b k ^ 2 * δ k ≤ F b := by
    intro k hk
    have h := hδ k ((b k)⁻¹ • b) (by simp [hk])
    rw [hF] at h
    have hk2 : 0 < b k ^ 2 := by positivity
    calc b k ^ 2 * δ k ≤ b k ^ 2 * ((b k)⁻¹ ^ 2 * F b) := mul_le_mul_of_nonneg_left h hk2.le
      _ = F b := by field_simp
  by_cases hj : b j = 0
  · rw [hj]
    by_cases h0 : b = 0
    · have := hF 0 0
      simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
      rw [h0, this]; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h0
      have := scaled k hk
      have : 0 ≤ b k ^ 2 * δ k := mul_nonneg (sq_nonneg _) (hδ0 k)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      linarith
  · exact scaled j hj

/-- Each coefficient obeys `|b j| ≤ √(F b)/√(δ j)`. -/
theorem abs_coef_le (hF : ∀ (t : ℝ) (b : ι → ℝ), F (t • b) = t ^ 2 * F b)
    (hδpos : ∀ j, 0 < δ j) (hδ : ∀ j (b : ι → ℝ), b j = 1 → δ j ≤ F b) (b : ι → ℝ) (j : ι) :
    |b j| ≤ √(F b) / √(δ j) := by
  have h := coef_sq_mul_le hF (fun k => (hδpos k).le) hδ b j
  rw [le_div_iff₀ (sqrt_pos.mpr (hδpos j)), ← sqrt_sq_eq_abs, ← sqrt_mul (sq_nonneg _)]
  exact sqrt_le_sqrt h

/-- A linear map obeys `‖T b‖ ≤ (Σ_j ‖T e_j‖/√(δ j)) √(F b)`. -/
theorem norm_le_of_floor [DecidableEq ι] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (hF : ∀ (t : ℝ) (b : ι → ℝ), F (t • b) = t ^ 2 * F b)
    (hδpos : ∀ j, 0 < δ j) (hδ : ∀ j (b : ι → ℝ), b j = 1 → δ j ≤ F b)
    (T : (ι → ℝ) →ₗ[ℝ] E) (b : ι → ℝ) :
    ‖T b‖ ≤ (∑ j, ‖T (Pi.single j 1)‖ / √(δ j)) * √(F b) := by
  have hb : b = ∑ j, b j • (Pi.single j 1 : ι → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hb, map_sum, ← hb, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  calc |b j| * ‖T (Pi.single j 1)‖ ≤ √(F b) / √(δ j) * ‖T (Pi.single j 1)‖ :=
        mul_le_mul_of_nonneg_right (abs_coef_le hF hδpos hδ b j) (norm_nonneg _)
    _ = ‖T (Pi.single j 1)‖ / √(δ j) * √(F b) := by ring

end General

section Spine

/-- The even first-cell energy `(1/(2x))∫_{(1/2,1]} (G + E_G/√(1/x))²` of a spine coefficient vector. -/
def cellEnergy (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  1 / (x : ℝ) / 2 * ∫ u in Ioc (1 / 2 : ℝ) 1,
    (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b u
      + eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) u / √(1 / (x : ℝ))) ^ 2

/-- The even first-cell energy is degree-2 homogeneous. -/
theorem cellEnergy_smul (x : ℕ) (t : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    cellEnergy x (t • b) = t ^ 2 * cellEnergy x b := by
  unfold cellEnergy
  rw [Cvs.Approximant.SpineSubspace.spineG_smul, Cvs.Xi.EImageWindowPoisson.eimage_smul]
  rw [show (fun u => (t * Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b u
        + t * eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) u / √(1 / (x : ℝ))) ^ 2)
      = fun u => t ^ 2 * (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b u
        + eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) u / √(1 / (x : ℝ))) ^ 2 by
    funext u; ring, integral_const_mul]
  ring

/-- A unit-coefficient floor on the even first-cell energy bounds any linear map of the spine coefficients by the
even part of the spine class: `‖T b‖ ≤ (Σ_j ‖T e_j‖/√(δ j)) ‖even part‖`. -/
theorem norm_le_of_cell_floor {x : ℕ} (hx : 80 ≤ 2 * π * x) {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (T : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] E) (δ : Cvs.Approximant.SpineSubspace.SF x → ℝ) (hδpos : ∀ j, 0 < δ j)
    (hδ : ∀ j (b : Cvs.Approximant.SpineSubspace.SF x → ℝ), b j = 1 → δ j ≤ cellEnergy x b) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖T b‖ ≤ (∑ j, ‖T (Pi.single j 1)‖ / √(δ j))
      * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x b)‖ := by
  refine (norm_le_of_floor (cellEnergy_smul x) hδpos hδ T b).trans
    (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun j _ => by positivity))
  exact (sqrt_le_sqrt (Cvs.Route.Visibility.EvenFirstCellProfile.norm_evenPart_spineMap_ge hx b)).trans_eq (sqrt_sq (norm_nonneg _))

end Spine

end Cvs.Upstream.CoefficientFloorLinearBound
