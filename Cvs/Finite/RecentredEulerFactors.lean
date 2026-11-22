import Mathlib
import Cvs.Finite.RecentredSecularLattice
import Cvs.Finite.RecentredTransform
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The recentred transform against the Euler factors

The lattice product `∏ (q_j - z²)` is `∏ q_j` times the normalised factors `∏ (1 - z² / q_j)`, so
off the lattice the recentred transform times `∏ q_j` times the Euler factors is `L sin (z L / 2)`
times `(z²)^t` times the shifted secular polynomial at `z²`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Polynomial Real

namespace Cvs.Finite.RecentredEulerFactors
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.ReducedSecularPolynomial
open Cvs.Finite.SecularCoefficientLimits Cvs.Limit.MomentSpineAlone

/-- **A squared frequency of the window is not zero.** -/
theorem qf_ne_zero {L : ℝ} (hL : L ≠ 0) (N : ℕ) (j : Fin N) : qf L N j ≠ 0 := by
  unfold qf
  have h : (2 * π * (((j : ℕ) : ℝ) + 1) / L : ℝ) ≠ 0 := by
    have hj : (((j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    exact div_ne_zero (mul_ne_zero hπ hj) hL
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr h)

/-- **The lattice product splits off its value at the origin.** -/
theorem prod_qf_sub {L : ℝ} (hL : L ≠ 0) (N : ℕ) (w : ℂ) :
    ∏ j : Fin N, (qf L N j - w) = (∏ j : Fin N, qf L N j) * ∏ j : Fin N, ((1 : ℂ) - w / qf L N j) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hq := qf_ne_zero hL N j
  field_simp

/-- **The recentred transform against the Euler factors.** -/
theorem cgtransform_mul_euler (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ}
    (hω : ∀ i : Idx N, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + z ≠ 0)
    (hz : z ^ 2 ≠ 0) (hq : ∀ j : Fin N, (qf L N j : ℂ) - z ^ 2 ≠ 0) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N z * (∏ j : Fin N, qf L N j)
        * (z * L / 2 * ∏ j : Fin N, ((1 : ℂ) - z ^ 2 / qf L N j))
      = L * Complex.sin (z * L / 2)
        * ((z ^ 2) ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
          * (shiftP (secPolyP L N (ground P R L hL N))).eval (z ^ 2)) := by
  have h := Cvs.Finite.RecentredSecularLattice.cgtransform_mul_lattice P R hL N hω hz hq
  rw [prod_qf_sub hL.ne' N (z ^ 2)] at h
  have hz1 : z ≠ 0 := fun h0 => hz (by rw [h0]; ring)
  have h2z : (-2 * z : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hz1
  apply mul_left_cancel₀ h2z
  linear_combination (L : ℂ) * h

end Cvs.Finite.RecentredEulerFactors
