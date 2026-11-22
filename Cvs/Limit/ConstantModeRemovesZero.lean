import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.MomentSpineConstantCoeff
import Cvs.Limit.OffAxisSpineChosenConstants
import Cvs.Limit.RecentredLocallyBoundedScalars
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A non-zero constant mode removes the secular polynomial's zero at the origin

The secular polynomial at the origin is the constant mode times the product of the squared
frequencies, so a non-zero constant mode makes the order of its zero there equal to zero, and the
local bound of `Cvs.Limit.RecentredLocallyBoundedScalars` then rests on two scalars.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Polynomial Real

namespace Cvs.Limit.ConstantModeRemovesZero
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.SecularCoefficientLimits

/-- **With a non-zero constant mode the secular polynomial does not vanish at the origin.** -/
theorem natTrailingDegree_secPolyP {L : ℝ} (hL : 0 < L) (N : ℕ) {xi : Idx N → ℝ}
    (h : xi none ≠ 0) : (secPolyP L N xi).natTrailingDegree = 0 := by
  refine Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr ?_)
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_secPolyP]
  exact Cvs.Limit.MomentSpineConstantCoeff.secPoly_zero_ne_zero hL N h

/-- **Local boundedness of the normalised recentred family, from two scalars and the constant
mode.** -/
theorem bdd_of_constant_mode {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) {w₀ : ℂ}
    (hw : w₀ ≠ 0) (hw₀ : (w₀ ^ 2).re = 0) (hN : ∀ n, 0 < N n) {K C : ℝ}
    (hS : ∀ n, ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots.map fun r => ‖r‖⁻¹).sum ≤ K)
    (hx0 : ∀ n, ground (P n) (R n) (L n) (hL n) (N n) none ≠ 0)
    (hC : ∀ n, L n ^ 2 / (N n : ℝ) ≤ C) :
    ∀ r : ℝ, ∃ M : ℝ, ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ r →
      ‖Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P n) (R n) (hL n) (N n) w₀
        * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z‖ ≤ M :=
  Cvs.Limit.RecentredLocallyBoundedScalars.bdd_of_scalars hL P R N hw hw₀ hN (T := 0) hS
    (fun n => (natTrailingDegree_secPolyP (hL n) (N n) (hx0 n)).le) hC

end Cvs.Limit.ConstantModeRemovesZero
