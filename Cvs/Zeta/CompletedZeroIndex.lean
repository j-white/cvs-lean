import Mathlib

/-!
# The completed zero-side gate

`BoundaryCompletedPlaceFunctional` assembles the place side without using zeta-zero data.
-/

namespace Cvs.Zeta.Explicit.Venue

open MeasureTheory

noncomputable section

/-- The nontrivial zeta zeros. Trivial negative-even zeros are excluded
because their contribution is already represented by the Gamma place. -/
def nontrivialRiemannZetaZeros :=
  {rho : riemannZetaZeros // 0 < (rho : ℂ).re ∧ (rho : ℂ).re < 1}

/-- Nontrivial zeta-zero multiplicity, obtained from analytic order. Every
index lies away from the zeta pole and hence in the analytic locus. -/
noncomputable def completedZetaZeroMultiplicity
    (rho : nontrivialRiemannZetaZeros) : ℕ :=
  analyticOrderNatAt riemannZeta ((rho.1 : riemannZetaZeros) : ℂ)

/-- Zeta zeros counted with analytic multiplicity. -/
def CompletedZetaZeroIndex :=
  Σ rho : nontrivialRiemannZetaZeros, Fin (completedZetaZeroMultiplicity rho)

end

end Cvs.Zeta.Explicit.Venue
