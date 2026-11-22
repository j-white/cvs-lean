import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformClosed
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
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
# The recentred transform is its secular polynomial at `z²`, over the lattice product

Off the lattice, the recentred transform times `-z² ∏ (q_j - z²)` is `-2 z sin (z L / 2)` times
the secular polynomial at `z²`, and that polynomial is `(z²)^t` times its shift, `t` being the
order of its zero at the origin.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Polynomial

namespace Cvs.Finite.RecentredSecularLattice
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.ReducedSecularPolynomial
open Cvs.Finite.SecularCoefficientLimits Cvs.Limit.MomentSpineAlone

/-- **A polynomial is a power of the variable times its shift**, evaluated. -/
theorem eval_eq_pow_mul_eval_shiftP (p : ℂ[X]) (w : ℂ) :
    p.eval w = w ^ p.natTrailingDegree * (shiftP p).eval w := by
  conv_lhs => rw [← X_pow_mul_shiftP p]
  rw [eval_mul, eval_pow, eval_X]

/-- **The recentred transform against the lattice product is the shifted secular polynomial.** -/
theorem cgtransform_mul_lattice (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ}
    (hω : ∀ i : Idx N, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + z ≠ 0)
    (hz : z ^ 2 ≠ 0) (hq : ∀ j : Fin N, (qf L N j : ℂ) - z ^ 2 ≠ 0) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N z * (-z ^ 2 * ∏ j, ((qf L N j : ℂ) - z ^ 2))
      = -2 * z * Complex.sin (z * L / 2)
        * ((z ^ 2) ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
          * (shiftP (secPolyP L N (ground P R L hL N))).eval (z ^ 2)) := by
  have h1 := Cvs.Finite.RecentredTransformClosed.cgtransform_eq_sin P R hL N hω
  have h2 := S_mul_eq_secPoly (L := L) N (ground P R L hL N) hz hq
  rw [← eval_eq_pow_mul_eval_shiftP, eval_secPolyP, ← h2, h1]
  ring

end Cvs.Finite.RecentredSecularLattice
