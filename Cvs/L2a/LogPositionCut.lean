import Mathlib
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.LogPositionDiagonal
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a by the log-position split with the off-diagonal cut hypothesis

As `Cvs.L2a.LogPositionDiagonal.L2a_logPos_diag`, with the residual hypothesis replaced by a cut weight `ω` (`0 ≤ ω ≤ log` on `[1,∞)`,
`ω = log` from some `t2 ≤ 2`) and `cutNS ≤ ε(−cutW) + C·N` with `ε ≤ 1`; `Cvs.L2a.CutWeightResidual.R_star_of_NS` turns this into
`diagD − logResid ≤ C·N`.
-/

namespace Cvs.L2a.LogPositionCut

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity Cvs.L2a.CutWeightResidual
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- **L2a by the log-position split, cut form**: low mass `≤ ηN`, the log-position sum bounded by the `log⁺`
arch mass plus `Lloc·N`, a cut weight with `cutNS ≤ ε(−cutW) + C·N` and the pole `≥ −qN` give
`(archSymbol T − 114/T − (archSymbol T − archSymbol 0)η − Lloc − C − q) N ≤ weilForm P R (logScale (posTail Φ X))`. -/
theorem L2a_logPos_cut (Φ ω : ℝ → ℝ) {X T η Lloc q t2 ε C : ℝ} (P R : ℕ) (hX : 1 ≤ X)
    (hΦ : ContDiffOn ℝ 1 Φ (Icc 1 X))
    (hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R)
    (hT : 2 ≤ T)
    (hlow : ∫ t in {t : ℝ | |t| < T}, specDensity (logScale (posTail Φ X)) t
      ≤ η * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hloc : logPos Φ X ≤ (∫ t, specDensity (logScale (posTail Φ X)) t * max 0 (Real.log (|t| / T)))
      + Lloc * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hω : ContinuousOn ω (Icc 1 X)) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωle : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) (hε1 : ε ≤ 1)
    (hNS : cutNS ω Φ X ≤ ε * (-(cutW ω Φ X)) + C * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, posTail Φ X θ) * (∫ θ in Ioi 1, posTail Φ X θ / θ)) :
    (archSymbol T - 114 / T - (archSymbol T - archSymbol 0) * η - Lloc - C - q)
        * (∫ θ in Ioi 1, posTail Φ X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (posTail Φ X)) :=
  Cvs.L2a.LogPositionDiagonal.L2a_logPos_diag Φ P R hX hΦ hPR hT hlow hloc
    (R_star_of_NS ω Φ hX hΦ.continuousOn hω hε1 ht2' hω0 hωle hωeq hNS) hpole

end Cvs.L2a.LogPositionCut
