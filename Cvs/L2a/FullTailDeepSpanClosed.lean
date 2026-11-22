import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.LocalResidualBound
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SecondModeShells
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full-tail L2a on the deep span, closed

For `c ≥ 10¹⁶`, `σᵢ² ≥ 5c`, the even span, `κ ≥ 1`, `T ≥ 2` and `∫₁³ ψᵢ² > 0`, the floor
`κ_F = kappaF 10¹⁶ c J (7/100)` is positive and gives `b̄·N(M) ≤ W(M)` at every integer `M ≥ 3` and
`b̄·N_∞ ≤ W_∞`; the `m = 2` shells come from `SecondModeShells`'s `shellM2_star`, the residual from `LocalResidualBound`'s `resLoc_le`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.FullTailDeepSpanClosed

/-- **The full-tail L2a on the deep span**: for `c ≥ 10¹⁶`, `σᵢ² ≥ 5c`, the even span, `κ ≥ 1`, `T ≥ 2` and
`∫₁³ ψᵢ² > 0`: `κ_F > 0`, `b̄·N(M) ≤ W(M)` at every integer `M ≥ 3`, and `b̄·∫₁^∞ fullTail(Φ)² ≤ W_∞(Φ)`,
with `κ_F = kappaF 10¹⁶ c J (7/100)`. -/
theorem L2a_fulltail_span_closed {ι : Type} [Fintype ι] {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ}
    {χ : ι → ℝ} (a : ι → ℝ) {κ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2) :
    0 < Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) (7 / 100)
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullTailDeepSpan.bBar c κ (Fintype.card ι)
              (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) (7 / 100))
            * (∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M θ ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M)))
      ∧ Cvs.L2a.FullTailDeepSpan.bBar c κ (Fintype.card ι)
            (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) (7 / 100))
          * (∫ θ in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
              (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) θ ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) :=
  Cvs.L2a.FullTailDeepSpan.L2a_fulltail_span a hg hg₁ hg₂c hang hc hχ0 hσ hχi heven hg0 hμ hidx hJ
    (Cvs.L2a.SecondModeShells.shellM2_star a hg hg₁ hg₂c hang hc hχ0 hσ hχi hmass)
    (fun _ hM => Cvs.L2a.LocalResidualBound.resLoc_le hc (Nat.cast_nonneg _) hJ hM) (by norm_num) hκ1 hT hmass

end Cvs.L2a.FullTailDeepSpanClosed
