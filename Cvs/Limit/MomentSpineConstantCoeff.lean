import Mathlib
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SymmetricModeSet

/-!
# The RH spine on the moments, assuming only a nonzero constant coefficient
`tendstoLocallyUniformly_of_realRooted`: polynomials with real nonzero roots whose normalised coefficients converge
termwise converge locally uniformly after normalisation at `0` — the first two coefficients bound all others
(`an earlier result`). The ground state's secular polynomial has real roots (`Cvs.Finite.ReducedSecularPolynomial`) and no root at `0` when `x₀ ≠ 0`
(`roots_real_ground`). `riemannHypothesis_of_moments'`: `x₀ ≠ 0` at every scale and moment limits `→ xiCoeff j` give RH.
-/

noncomputable section

open Polynomial Filter Topology Finset

namespace Cvs.Limit.MomentSpineConstantCoeff
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Finite.ReducedSecularPolynomial

theorem secPoly_zero_ne_zero {L : ℝ} (hL : 0 < L) (N : ℕ) {xi : Idx N → ℝ} (h : xi none ≠ 0) :
    secPoly L N xi 0 ≠ 0 := by
  rw [secPoly_zero]
  refine mul_ne_zero (by exact_mod_cast h) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  unfold qf
  refine pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ?_)
  exact (div_pos (by positivity) hL).ne'

end Cvs.Limit.MomentSpineConstantCoeff
