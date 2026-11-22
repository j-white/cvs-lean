import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineChosenConstants
import Cvs.Limit.RecentredPointwiseBound
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The normalised recentred family is locally bounded, from three scalars

Normalise at a non-zero point `w₀` whose square is purely imaginary.  If along the sequence the
reciprocal moduli of the secular roots sum to at most `K`, the order of the secular polynomial's
zero at the origin is at most `T`, and `L² / N` is at most `C`, then on the ball of radius `r` the
family is at most `max 1 (r² / ‖w₀²‖) ^ T * exp (r² K) * exp (r² C / (4 π²))`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Polynomial Real

namespace Cvs.Limit.RecentredLocallyBoundedScalars
open Cvs.ZeroCounting

open Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.SecularCoefficientLimits Cvs.Limit.MomentSpineAlone

/-- **Local boundedness of the normalised recentred family, from three scalars.** -/
theorem bdd_of_scalars {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) {w₀ : ℂ}
    (hw : w₀ ≠ 0) (hw₀ : (w₀ ^ 2).re = 0) (hN : ∀ n, 0 < N n) {K C : ℝ} {T : ℕ}
    (hS : ∀ n, ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots.map fun r => ‖r‖⁻¹).sum ≤ K)
    (hT : ∀ n, (secPolyP (L n) (N n)
      (ground (P n) (R n) (L n) (hL n) (N n))).natTrailingDegree ≤ T)
    (hC : ∀ n, L n ^ 2 / (N n : ℝ) ≤ C) :
    ∀ r : ℝ, ∃ M : ℝ, ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ r →
      ‖Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P n) (R n) (hL n) (N n) w₀
        * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z‖ ≤ M := by
  intro r
  have hc : 0 < ‖w₀ ^ 2‖ := norm_pos_iff.mpr (pow_ne_zero 2 hw)
  refine ⟨max 1 (r ^ 2 / ‖w₀ ^ 2‖) ^ T * exp (r ^ 2 * K) * exp (r ^ 2 * C / (4 * π ^ 2)),
    fun n z hz => ?_⟩
  have hwoff := Cvs.Limit.RecentredPointwiseBound.offAxes_of_sq_re_zero hw hw₀
  have hb : 0 < ‖Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) w₀‖ :=
    norm_pos_iff.mpr (Cvs.Finite.RecentredTransform.cgtransform_ne_zero (P n) (R n) (hL n) (N n) hwoff)
  have hmain := Cvs.Limit.RecentredPointwiseBound.norm_cgtransform_le (P n) (R n) (hL n) (hN n) hw hw₀ z
  set a := ‖Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z‖
  set b := ‖Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) w₀‖
  set t := (secPolyP (L n) (N n) (ground (P n) (R n) (L n) (hL n) (N n))).natTrailingDegree
  set S := ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots.map fun r => ‖r‖⁻¹).sum
  set c := ‖w₀ ^ 2‖
  have hz2 : ‖z ^ 2‖ ≤ r ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hS0 : 0 ≤ S := Multiset.sum_nonneg fun x hx => by
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
    positivity
  -- the norm of the normalised value
  have hnorm : ‖Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P n) (R n) (hL n) (N n) w₀
      * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z‖ = b⁻¹ * a := by
    unfold Cvs.Limit.OffAxisSpineChosenConstants.cnorm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  rw [hnorm]
  -- divide the pointwise bound through
  set q := ‖z ^ 2‖ / c
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hc.le
  have hqpow : c ^ t * q ^ t = ‖z ^ 2‖ ^ t := by
    rw [← mul_pow, mul_div_cancel₀ _ hc.ne']
  have hpt : b⁻¹ * a ≤ q ^ t * exp (‖z ^ 2‖ * S) * exp (‖z * (L n) / (2 * π)‖ ^ 2 / (N n)) := by
    have hpos : 0 < b * c ^ t := mul_pos hb (pow_pos hc t)
    refine le_of_mul_le_mul_left ?_ hpos
    calc b * c ^ t * (b⁻¹ * a) = a * c ^ t := by field_simp
      _ ≤ b * ‖z ^ 2‖ ^ t * exp (‖z ^ 2‖ * S) * exp (‖z * (L n) / (2 * π)‖ ^ 2 / (N n)) := hmain
      _ = b * c ^ t * (q ^ t * exp (‖z ^ 2‖ * S)
            * exp (‖z * (L n) / (2 * π)‖ ^ 2 / (N n))) := by rw [← hqpow]; ring
  -- the three factors
  have h1 : q ^ t ≤ max 1 (r ^ 2 / c) ^ T := by
    have hq : q ≤ max 1 (r ^ 2 / c) :=
      le_trans (div_le_div_of_nonneg_right hz2 hc.le) (le_max_right _ _)
    exact le_trans (pow_le_pow_left₀ hq0 hq t) (pow_le_pow_right₀ (le_max_left _ _) (hT n))
  have h2 : exp (‖z ^ 2‖ * S) ≤ exp (r ^ 2 * K) :=
    exp_le_exp.mpr (mul_le_mul hz2 (hS n) hS0 (by positivity))
  have h3 : exp (‖z * (L n) / (2 * π)‖ ^ 2 / (N n)) ≤ exp (r ^ 2 * C / (4 * π ^ 2)) := by
    apply exp_le_exp.mpr
    have hform : z * (L n : ℂ) / (2 * (π : ℂ)) = z * (((L n / (2 * π) : ℝ)) : ℂ) := by
      push_cast; ring
    have hLpos : 0 < L n / (2 * π) := by have := hL n; positivity
    rw [hform, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast hN n
    have heq : (‖z‖ * (L n / (2 * π))) ^ 2 / (N n : ℝ)
        = ‖z‖ ^ 2 * (L n ^ 2 / (N n : ℝ)) / (4 * π ^ 2) := by
      field_simp
      ring
    rw [heq]
    have hzz : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    exact div_le_div_of_nonneg_right
      (mul_le_mul hzz (hC n) (by have := hL n; positivity) (by positivity)) (by positivity)
  calc b⁻¹ * a ≤ q ^ t * exp (‖z ^ 2‖ * S) * exp (‖z * (L n) / (2 * π)‖ ^ 2 / (N n)) := hpt
    _ ≤ max 1 (r ^ 2 / c) ^ T * exp (r ^ 2 * K) * exp (r ^ 2 * C / (4 * π ^ 2)) := by
        gcongr

end Cvs.Limit.RecentredLocallyBoundedScalars
