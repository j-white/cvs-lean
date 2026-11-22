import Mathlib
import Cvs.Zeta.CompletedZeroIndex

/-!
# The divisor weight costs nothing: from the expansion to the weighted sum

`an earlier result` proved the zero side summable over `Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex`, the
multiplicity expansion.
-/

namespace Cvs.Criterion

open scoped BigOperators

/-- **The weight is the fibre cardinality.**  A function pulled back from the base sums over
one fibre to the multiplicity times its value. -/
theorem tsum_fibre {g : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros → ℝ}
    (rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros) :
    (∑' _i : Fin (Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity rho), g rho)
      = (Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity rho : ℝ) * g rho := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Summability on the multiplicity expansion gives summability at the divisor weight.**
No bound on the multiplicity is used, and none is available. -/
theorem summable_weighted_of_sigma
    {g : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros → ℝ}
    (h : Summable fun rho : Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex => g rho.1) :
    Summable fun rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros =>
      (Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity rho : ℝ) * g rho := by
  have hs : Summable fun rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros =>
      ∑' _i : Fin (Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity rho), g rho :=
    Summable.sigma (f := fun rho : Σ rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros,
      Fin (Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity rho) => g rho.1) h
  simpa only [tsum_fibre] using hs

end Cvs.Criterion
