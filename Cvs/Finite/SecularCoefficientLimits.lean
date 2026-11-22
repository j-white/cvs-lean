import Mathlib
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SymmetricModeSet

/-!
# Step (b) as coefficient limits of the ground-state secular polynomial
`secPolyP` is `Cvs.Finite.ReducedSecularPolynomial.secPoly` as a polynomial. If it has no root on `(−∞, 0]` (`NoNonposRoot`), every root is real and
positive (`roots_pos_ground`: non-real roots are excluded by `Cvs.Finite.ReducedSecularPolynomial`), so its normalised coefficients are
`(−1)^j e_j(1/r)` (`coeff_div_eval_zero`). `riemannHypothesis_of_coeff`: with that sign condition at every scale, if the
normalised coefficients converge to `g_j` and `∑ g_j z^{2j}` vanishes at the off-axis zeros of `Ξ`, RH follows.
-/

noncomputable section

open Polynomial Filter Topology Finset

namespace Cvs.Finite.SecularCoefficientLimits
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Finite.ReducedSecularPolynomial

/-- The reduced secular polynomial as a polynomial. -/
def secPolyP (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) : ℂ[X] :=
  C (xi none : ℂ) * ∏ j, (C (qf L N j) - X)
    + ∑ j, C (((xi (some (j, true)) + xi (some (j, false)) : ℝ) : ℂ)) * (-X)
        * ∏ j' ∈ Finset.univ.erase j, (C (qf L N j') - X)

theorem eval_secPolyP (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) (w : ℂ) :
    (secPolyP L N xi).eval w = secPoly L N xi w := by
  simp [secPolyP, secPoly, eval_prod, eval_finsetSum]

/-- No root on the closed negative axis: `x₀ ≠ 0` and no zero of the transform on the imaginary axis. -/
def NoNonposRoot (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) : Prop :=
  ∀ t : ℝ, t ≤ 0 → secPoly L N xi (t : ℂ) ≠ 0

end Cvs.Finite.SecularCoefficientLimits
