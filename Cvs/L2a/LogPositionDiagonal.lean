import Mathlib
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PartOneWeilForm
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTailPrimePairs
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.GradedArchFloor
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a by the log-position split with the diagonal-minus-residual hypothesis

As `an earlier result.L2a_logPos`, but the residual hypothesis is `diagD − logResid ≤ CR·N` (the prime side is
`logPos + diagD − logResid` exactly by `Cvs.L2a.LogPositionIdentity.pairs_eq`); an earlier result's `−logResid ≤ CR·N` implies it since `diagD ≤ 0`.
-/

namespace Cvs.L2a.LogPositionDiagonal

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- **L2a by the log-position split, diagonal form**: low mass `≤ ηN`, the log-position sum bounded by the `log⁺`
arch mass plus `Lloc·N`, `diagD − logResid ≤ CR·N` and the pole `≥ −qN` give
`(archSymbol T − 114/T − (archSymbol T − archSymbol 0)η − Lloc − CR − q) N ≤ weilForm P R (logScale (posTail Φ X))`. -/
theorem L2a_logPos_diag (Φ : ℝ → ℝ) {X T η Lloc CR q : ℝ} (P R : ℕ) (hX : 1 ≤ X)
    (hΦ : ContDiffOn ℝ 1 Φ (Icc 1 X))
    (hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R)
    (hT : 2 ≤ T)
    (hlow : ∫ t in {t : ℝ | |t| < T}, specDensity (logScale (posTail Φ X)) t
      ≤ η * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hloc : logPos Φ X ≤ (∫ t, specDensity (logScale (posTail Φ X)) t * max 0 (Real.log (|t| / T)))
      + Lloc * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hR : diagD Φ X - logResid Φ X ≤ CR * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, posTail Φ X θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, posTail Φ X θ) * (∫ θ in Ioi 1, posTail Φ X θ / θ)) :
    (archSymbol T - 114 / T - (archSymbol T - archSymbol 0) * η - Lloc - CR - q)
        * (∫ θ in Ioi 1, posTail Φ X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (posTail Φ X)) := by
  set F := posTail Φ X with hFdef
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hNdef
  set f := logScale F with hfdef
  have hF : ∀ θ ≤ 1, F θ = 0 := fun θ hθ => posTail_zero Φ X hθ
  obtain ⟨h2, h1, hsq, hsh, hlevy⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX hΦ
  have hNf : ∫ s, f s ^ 2 = N := integral_sq F hF
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have hspec := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch h2 h1 hlevy
  have hA := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul h2 h1 hlevy
  have hρN : ∫ t, specDensity f t = N := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2, hNf]
  -- the archimedean channel
  have harch := Cvs.L2a.PartOneWeilForm.arch_eq h2 h1 hsq hsh hlevy hspec hρ
  have hgr := Cvs.WeilForm.Archimedean.GradedArchFloor.integral_arch_ge_graded (specDensity f)
    (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t) hρ hA hT
  rw [hρN] at hgr
  have hgap := Cvs.WeilForm.Archimedean.GradedArchFloor.archSymbol_sub_zero_nonneg T
  have hlow' : (archSymbol T - archSymbol 0) * (∫ t in {t : ℝ | |t| < T}, specDensity f t)
      ≤ (archSymbol T - archSymbol 0) * (η * N) := mul_le_mul_of_nonneg_left hlow hgap
  -- the prime side, exactly `logPos + diagD − logResid`
  have hprime : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution f)
      = logPos Φ X + diagD Φ X - logResid Φ X := by
    rw [hfdef, hFdef, Cvs.L2a.PositionTailPrimePairs.primeSide_posTail Φ hX hΦ.continuousOn P R hPR]
    exact pairs_eq Φ hX hΦ.continuousOn
  -- the pole
  have hpole' : -(q * N)
      ≤ 2 * (∫ s, f s * exp (s / 2)) * (∫ s, f s * exp (-(s / 2))) := by
    rw [integral_mul_exp F hF, integral_mul_exp_neg F hF]; exact hpole
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, harch]
  linarith

end Cvs.L2a.LogPositionDiagonal
