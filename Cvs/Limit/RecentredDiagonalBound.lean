import Mathlib
import Cvs.Finite.RecentredEulerFactors
import Cvs.Finite.RecentredTransform
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Upstream.PolyControlledByRootReciprocals
import Cvs.Upstream.SineDiagonalLowerBound
import Cvs.Upstream.SineEulerFactorsBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The recentred transform, normalised on a diagonal, is bounded by its roots and the tail

Off the lattice, the transform at `z` against the transform at a point `w₀` with `w₀²` purely
imaginary is at most the ratio of the powers `‖z²‖^t`, times `exp (‖z²‖ ∑ 1 / ‖ρ‖)` over the
roots of the shifted secular polynomial, times the sine tail `exp (‖z L / (2 π)‖² / N)`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Polynomial Real

namespace Cvs.Limit.RecentredDiagonalBound
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.ReducedSecularPolynomial
open Cvs.Finite.SecularCoefficientLimits Cvs.Limit.MomentSpineAlone Cvs.Finite.RecentredEulerFactors

/-- The Euler factors in the window's variable. -/
def euler (L : ℝ) (N : ℕ) (z : ℂ) : ℂ := z * L / 2 * ∏ j : Fin N, ((1 : ℂ) - z ^ 2 / qf L N j)

/-- **Off the lattice the Euler factors do not vanish.** -/
theorem euler_ne_zero {L : ℝ} (hL : L ≠ 0) (N : ℕ) {z : ℂ} (hz : z ^ 2 ≠ 0)
    (hq : ∀ j : Fin N, (qf L N j : ℂ) - z ^ 2 ≠ 0) : euler L N z ≠ 0 := by
  unfold euler
  have hz1 : z ≠ 0 := fun h0 => hz (by rw [h0]; ring)
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  refine mul_ne_zero (div_ne_zero (mul_ne_zero hz1 hLc) (by norm_num)) ?_
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  have hqj := qf_ne_zero hL N j
  have : (1 : ℂ) - z ^ 2 / qf L N j = (qf L N j - z ^ 2) / qf L N j := by field_simp
  rw [this]
  exact div_ne_zero (hq j) hqj

/-- **The sine is at most the Euler factors times the tail.** -/
theorem norm_sin_le_euler {L : ℝ} (hL : L ≠ 0) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    ‖Complex.sin (z * L / 2)‖ ≤ ‖euler L N z‖ * exp (‖z * L / (2 * π)‖ ^ 2 / N) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπu : (π : ℂ) * (z * L / (2 * π)) = z * L / 2 := by field_simp
  have h := Cvs.Upstream.SineEulerFactorsBound.norm_sin_le hN (z * L / (2 * π))
  rw [Cvs.Upstream.SineDiagonalLowerBound.euler_factors_eq hL N z, hπu] at h
  exact h

/-- **On a diagonal the Euler factors are at most the sine.** -/
theorem norm_euler_le_sin {L : ℝ} (hL : L ≠ 0) (N : ℕ) {w₀ : ℂ} (hw₀ : (w₀ ^ 2).re = 0) :
    ‖euler L N w₀‖ ≤ ‖Complex.sin (w₀ * L / 2)‖ := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπu : (π : ℂ) * (w₀ * L / (2 * π)) = w₀ * L / 2 := by field_simp
  have hsq : (w₀ * L / (2 * π)) ^ 2 = w₀ ^ 2 * (((L / (2 * π)) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hre : ((w₀ * L / (2 * π)) ^ 2).re ≤ 0 := by
    rw [hsq, Complex.re_mul_ofReal, hw₀, zero_mul]
  have h := Cvs.Upstream.SineDiagonalLowerBound.le_norm_sin hre N
  rw [Cvs.Upstream.SineDiagonalLowerBound.euler_factors_eq hL N w₀, hπu] at h
  exact h

/-- **The pointwise bound, off the lattice.** -/
theorem norm_cgtransform_le (P R : ℕ) {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N) {z w₀ : ℂ}
    (hωz : ∀ i : Idx N, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + z ≠ 0)
    (hz : z ^ 2 ≠ 0) (hqz : ∀ j : Fin N, (qf L N j : ℂ) - z ^ 2 ≠ 0)
    (hωw : ∀ i : Idx N, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + w₀ ≠ 0)
    (hw : w₀ ^ 2 ≠ 0) (hqw : ∀ j : Fin N, (qf L N j : ℂ) - w₀ ^ 2 ≠ 0)
    (hw₀ : (w₀ ^ 2).re = 0) :
    ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖
        * ‖w₀ ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
      ≤ ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖
        * ‖z ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
        * exp (‖z ^ 2‖ * ((shiftP (secPolyP L N (ground P R L hL N))).roots.map
            fun r => ‖r‖⁻¹).sum)
        * exp (‖z * L / (2 * π)‖ ^ 2 / N) := by
  set G := shiftP (secPolyP L N (ground P R L hL N)) with hGdef
  set t := (secPolyP L N (ground P R L hL N)).natTrailingDegree with ht
  set Q : ℂ := ∏ j : Fin N, qf L N j with hQ
  have hQ0 : 0 < ‖Q‖ := norm_pos_iff.mpr
    (Finset.prod_ne_zero_iff.mpr fun j _ => qf_ne_zero hL.ne' N j)
  have he : 0 < ‖euler L N z‖ := norm_pos_iff.mpr (euler_ne_zero hL.ne' N hz hqz)
  have he0 : 0 < ‖euler L N w₀‖ := norm_pos_iff.mpr (euler_ne_zero hL.ne' N hw hqw)
  have hLn : ‖(L : ℂ)‖ = L := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  -- the two identities, in norms
  have hA : ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖ * ‖Q‖ * ‖euler L N z‖
      = L * ‖Complex.sin (z * L / 2)‖ * (‖z ^ 2‖ ^ t * ‖G.eval (z ^ 2)‖) := by
    have h := congrArg norm (cgtransform_mul_euler P R hL N hωz hz hqz)
    simpa only [norm_mul, norm_pow, hLn, euler] using h
  have hB : ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖ * ‖Q‖ * ‖euler L N w₀‖
      = L * ‖Complex.sin (w₀ * L / 2)‖ * (‖w₀ ^ 2‖ ^ t * ‖G.eval (w₀ ^ 2)‖) := by
    have h := congrArg norm (cgtransform_mul_euler P R hL N hωw hw hqw)
    simpa only [norm_mul, norm_pow, hLn, euler] using h
  -- the three bounds
  have hs := norm_sin_le_euler hL.ne' hN z
  have hs0 := norm_euler_le_sin hL.ne' N hw₀
  have hG : ‖G.eval (z ^ 2)‖ ≤ ‖G.eval (w₀ ^ 2)‖
      * exp (‖z ^ 2‖ * (G.roots.map fun r => ‖r‖⁻¹).sum) :=
    Cvs.Upstream.PolyControlledByRootReciprocals.norm_eval_gpoly_le (L := fun _ => L) (fun _ => hL) (fun _ => P)
      (fun _ => R) (fun _ => N) 0 hw₀ (z ^ 2)
  set a := ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖
  set b := ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖
  set X := exp (‖z * L / (2 * π)‖ ^ 2 / N)
  set Y := exp (‖z ^ 2‖ * (G.roots.map fun r => ‖r‖⁻¹).sum)
  set g0 := ‖G.eval (w₀ ^ 2)‖
  have hX : 0 < X := exp_pos _
  have hY : 0 < Y := exp_pos _
  -- A: cancel the Euler factors at z
  have hstepA : a * ‖Q‖ ≤ L * X * ‖z ^ 2‖ ^ t * g0 * Y := by
    refine le_of_mul_le_mul_right ?_ he
    rw [hA]
    calc L * ‖Complex.sin (z * L / 2)‖ * (‖z ^ 2‖ ^ t * ‖G.eval (z ^ 2)‖)
        ≤ L * (‖euler L N z‖ * X) * (‖z ^ 2‖ ^ t * (g0 * Y)) := by gcongr
      _ = L * X * ‖z ^ 2‖ ^ t * g0 * Y * ‖euler L N z‖ := by ring
  -- B: cancel the Euler factors at w₀
  have hstepB : L * ‖w₀ ^ 2‖ ^ t * g0 ≤ b * ‖Q‖ := by
    refine le_of_mul_le_mul_right ?_ he0
    rw [hB]
    calc L * ‖w₀ ^ 2‖ ^ t * g0 * ‖euler L N w₀‖
        = L * ‖euler L N w₀‖ * (‖w₀ ^ 2‖ ^ t * g0) := by ring
      _ ≤ L * ‖Complex.sin (w₀ * L / 2)‖ * (‖w₀ ^ 2‖ ^ t * g0) := by gcongr
  -- C: combine, and cancel ‖Q‖
  refine le_of_mul_le_mul_right ?_ hQ0
  calc a * ‖w₀ ^ 2‖ ^ t * ‖Q‖ = a * ‖Q‖ * ‖w₀ ^ 2‖ ^ t := by ring
    _ ≤ L * X * ‖z ^ 2‖ ^ t * g0 * Y * ‖w₀ ^ 2‖ ^ t := by gcongr
    _ = L * ‖w₀ ^ 2‖ ^ t * g0 * (‖z ^ 2‖ ^ t * Y * X) := by ring
    _ ≤ b * ‖Q‖ * (‖z ^ 2‖ ^ t * Y * X) := by gcongr
    _ = b * ‖z ^ 2‖ ^ t * Y * X * ‖Q‖ := by ring

end Cvs.Limit.RecentredDiagonalBound
