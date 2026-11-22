import Mathlib
import Cvs.Upstream.GammaEulerLimit
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyRepresentation
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.Zeta.Digamma

/-!
# The digamma limit, discharged

    ψ(s) = lim_n (log n − ∑_{k<n} 1/(s+k))    for `0 < re s`

`Cvs.Zeta.DigammaEulerLimitRe` was an isolated analytic input; `Cvs.Upstream.GammaEulerLimit`
proves it, so the blocks that assumed it are unconditional.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology

namespace Cvs.Zeta.DigammaLimitDischarged

/-- **The Euler–Gauss limit at the criterion's base point**, for every `t`. -/
instance instDigammaEulerLimitRe (t : ℝ) : Cvs.Zeta.DigammaEulerLimitRe t := by
  constructor
  have hre : 0 < (Cvs.Zeta.digammaArg t 0).re := Cvs.Zeta.digammaArg_re_pos t
  have h := Cvs.Upstream.GammaEulerLimit.tendsto_re_digamma hre
  refine h.congr fun n => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Cvs.Zeta.digammaArg_eq_add t k]

/-! ### The consequences, with the hypothesis gone -/

open MeasureTheory Set in
/-- **The archimedean Lévy representation, unconditionally.** -/
theorem integral_rep (t : ℝ) :
    (∫ u in Ioi (0:ℝ), (1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      = (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
        - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re :=
  Cvs.WeilForm.Archimedean.LevyRepresentation.integral_rep t

/-- **The symbol's increment is nonnegative, unconditionally.** -/
theorem sub_nonneg (t : ℝ) :
    0 ≤ (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
      - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re :=
  Cvs.WeilForm.Archimedean.LevyTermsSum.sub_nonneg_of_limit t

end Cvs.Zeta.DigammaLimitDischarged
