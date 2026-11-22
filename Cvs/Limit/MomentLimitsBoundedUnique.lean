import Mathlib
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.SpineWithoutSimplicity

/-!
# The moment limits from boundedness and uniqueness
Bounds on the first two normalised coefficients of a polynomial with real nonzero roots bound all of them, so along
a sequence of such polynomials (A1) and (A2) give convergence of every coefficient, by compactness of a product of
discs. Both hypotheses carry arithmetic content: a planted off-line zero leaves the minimiser real-rooted while
collapsing the local values near the origin, so (A1) fails exactly where an off-line zero appears.
-/

noncomputable section

open Polynomial Filter Topology Finset

namespace Cvs.Limit.MomentLimitsBoundedUnique
open Cvs.ZeroCounting

/-- The ground-state polynomial with its zeros at the origin removed. -/
def gpoly {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (n : ℕ) : ℂ[X] :=
  Cvs.Limit.MomentSpineAlone.shiftP (Cvs.Finite.SecularCoefficientLimits.secPolyP (L n) (N n)
    (Cvs.Limit.SpineWithoutSimplicity.ground (P n) (R n) (L n) (hL n) (N n)))

end Cvs.Limit.MomentLimitsBoundedUnique
