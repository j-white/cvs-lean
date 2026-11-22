import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.BandSumThreshold
import Cvs.L2a.FullSpanInstance
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.JointMainTerm
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.PlungeMassTrace
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a-FULL on `Finset.range x` from the top and bulk inputs of the E-coupling
Cvs.L2a.BandInputsFromCutMultipliers turns `TopInput x a` (`|topE| ≤ T√P`, `T ≤ 10⁶F_jc^{−3/4}`) and `BulkInput x a` (`|bulkE| ≤ (700F_j/c)√P`)
into `BandInputs x a 1`; `FullSpanInstance`'s instance at `K_r = 1` then gives L2a-FULL on the prolate span at `c = 2πx ≥ c₀^F`
with these two inputs as the only hypotheses beyond the scale.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FullSpanFromTopBulkInputs

open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.L2a.FullSpanInstance (kappaFfullG)
open Cvs.L2a.BandInputsFromCutMultipliers (TopInput BulkInput)

/-- **L2a-FULL on `Finset.range x` from the cut inputs**: past `c₀^F`, `TopInput x a` and `BulkInput x a` give
`FullSpanInstance`'s conclusion at `K_r = 1`: `κ_F ≥ 1/38`, `b̄ ≥ 1`, `b̄·N(M) ≤ W(M)` for all `M ≥ 3` and `b̄·N_∞ ≤ W_∞`. -/
theorem L2a_full_span_of_cuts (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x)
    (a : Finset.range x → ℝ) (htop : TopInput x a) (hbulk : BulkInput x a) :
    let c := 2 * π * x
    let Φ := fun ξ => ∑ j, a j * psi c (rung c (2 * (j : ℕ))) ξ
    let κF := kappaFfullG (10 ^ 16) c x (7 * c ^ (-(1 / 8 : ℝ))) (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      (Cvs.L2a.BandCouplingDischarged.thetaBar
        (Cvs.L2a.BandSumThreshold.kapBarG c 10
          (Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + Cvs.L2a.BandECouplingCollar.omegaE 1 c) ^ 2))
        (Cvs.Prolate.PlungeMassTrace.plungeBound c))
      (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ
    1 / 38 ≤ κF
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
      ∧ (∀ M : ℕ, 3 ≤ M →
          Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
              * ∫ y in Ioi 1, posTail Φ M y ^ 2
            ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
                (Cvs.L2a.TailLogScaleTest.logScale (posTail Φ M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
          * ∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail Φ y ^ 2
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf Φ :=
  Cvs.L2a.FullSpanInstance.L2a_full_span_instance x hx a zero_le_one (by norm_num)
    (Cvs.L2a.BandInputsFromCutMultipliers.bandInputs_of_cuts hx htop hbulk)

end Cvs.L2a.FullSpanFromTopBulkInputs
