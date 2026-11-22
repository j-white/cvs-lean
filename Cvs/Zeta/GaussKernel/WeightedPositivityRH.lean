import Mathlib
import Cvs.Zeta.ExplicitFormula.WeightedZeroSide
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.BumpAlgebra
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.WeightedChain
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-!
# Simplicity leaves the route
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel

/-- **Weighted positivity gives the weighted failure.** As in, the `lam` the frequently-statement
produces can be taken positive. -/
theorem weightedFail_of_positivity
    (hpos : ∀ lam a : ℝ, 0 < lam →
      0 ≤ Cvs.Zeta.ExplicitFormula.WeightedZeroSide.weilZeroSideWeighted Cvs.Criterion.divisorWeight lam a) :
    Cvs.Criterion.WeightedFail := by
  intro a hfreq
  obtain ⟨lam, hlt, hlpos⟩ :=
    (hfreq.and_eventually (Filter.eventually_gt_atTop (0 : ℝ))).exists
  have hge := hpos lam a hlpos
  have hcong : ∀ rho : nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ) * Cvs.Zeta.ExplicitFormula.WeightedZeroSide.summand lam a rho
        = (Cvs.Criterion.divisorWeight rho : ℝ)
          * (gaussAmp lam a ((gam rho : ℂ) - (del rho : ℂ) * Complex.I) ^ 2).re := by
    intro rho
    rw [Cvs.Zeta.ExplicitFormula.WeightedZeroSide.summand, weilSummand_gaussAmp lam a (rho : ℂ)]
    simp only [gam, del]
  rw [Cvs.Zeta.ExplicitFormula.WeightedZeroSide.weilZeroSideWeighted_eq, tsum_congr hcong] at hge
  exact absurd hlt (not_lt.mpr hge)

/-- Weighted positivity at the divisor weight, at the parameters where it has content. -/
def WeightedPositivityPos : Prop :=
  ∀ lam a : ℝ, 0 < lam → 0 ≤ Cvs.Zeta.ExplicitFormula.WeightedZeroSide.weilZeroSideWeighted Cvs.Criterion.divisorWeight lam a

/-- **Weighted positivity at the divisor weight implies RH.**  No simplicity, and no bound on
the multiplicity. -/
theorem riemannHypothesis_of_weightedPositivity (hpos : WeightedPositivityPos) :
    Cvs.Zeta.GaussKernel.AdmissibleKernel.riemannHypothesis :=
  Cvs.GaussKernel.riemannHypothesis_of_card
    (fun _ hg n => Cvs.Criterion.card_le_of_weighted_fail (weightedFail_of_positivity hpos) hg n)

end Cvs.Criterion
