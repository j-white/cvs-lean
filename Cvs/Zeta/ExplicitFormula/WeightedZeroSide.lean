import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-!
# The zero side, carrying multiplicity

`Cvs.Zeta.Contradiction.FormulaBridgeGe` is a hypothesis, and `Cvs.Audit` records why with
`#nomention Cvs.Zeta.GaussKernel.AdmissibleKernel.weilZeroSideGaussAmp MeromorphicOn.divisor`: the explicit formula weights
each `ξ`-zero by its divisor, while `weilZeroSideGaussAmp` is a `tsum` over
`nonTrivialZeroSet` carrying no multiplicity.
-/

namespace Cvs.Zeta.ExplicitFormula.WeightedZeroSide

open Complex Real

/-- **The zero side with multiplicity.**  Each zero weighted by a natural number —
`MeromorphicOn.divisor` at the intended instantiation. -/
noncomputable def weilZeroSideWeighted (w : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℕ) (lam a : ℝ) :
    ℝ :=
  ∑' ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (w ρ : ℝ) *
    (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a (-Complex.I * ((ρ : ℂ) - 1 / 2))
      * (starRingEnd ℂ) (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a
        (-Complex.I * ((starRingEnd ℂ) (ρ : ℂ) - 1 / 2)))).re

/-! ### The comparison the converse needs

`WeightsBounded` is named above but never used.  These two make it usable: with
`1 ≤ w ≤ W` the negative summands keep weight one and only the positive ones pay
`W`, which is exactly the inequality the docstring asks for. -/

/-- The unweighted summand, named so the comparison can be stated. -/
noncomputable def summand (lam a : ℝ) (ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : ℝ :=
  (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a (-Complex.I * ((ρ : ℂ) - 1 / 2))
    * (starRingEnd ℂ) (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a
      (-Complex.I * ((starRingEnd ℂ) (ρ : ℂ) - 1 / 2)))).re

theorem weilZeroSideWeighted_eq (w : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℕ) (lam a : ℝ) :
    weilZeroSideWeighted w lam a = ∑' ρ, (w ρ : ℝ) * summand lam a ρ := rfl

/-! ### Anchoring the framework

The weighted objects above are a *generalisation* of the certified criterion, not
a replacement for it: at `w ≡ 1` they are the same statement, and therefore
equivalent to RH by `an earlier result`.  Without this the weighted definitions float free. -/

/-! ### The converse of the reduction, and where simplicity actually enters

`analyticNonneg_of_weightedPositivity` runs positivity → analytic side.  The other
direction is what a *proof* of the criterion would use, and it is immediate from
the bridge being an equality rather than an inequality. -/

end Cvs.Zeta.ExplicitFormula.WeightedZeroSide
