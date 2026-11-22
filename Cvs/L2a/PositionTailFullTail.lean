import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.LogPositionCut
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanPole
import Cvs.L2a.SpectralMassLevelLeak
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
# L2a on the position-truncated full tail of the rung span

`Cvs.L2a.LogPositionCut.L2a_logPos_cut` on `Φ = Σ aᵢψᵢ` with every prime power `≤ X`, the pole from `Cvs.L2a.RungSpanPole.pole_span` (frame floor `κ_F`)
and `logPos` from the per-level far leak `ε(k)` (`Cvs.L2a.SpectralMassLevelLeak.hloc_of_levels`): the Weil form of the tail is at least
`(a(T) − 114/T − (a(T) − a₀)η − (log k₁ + ∫_{k₁}^X min(1, 2√ε)/k) − C − 49(c/4 + 1)/(2c²κ_F))·∫F²`.
-/

namespace Cvs.L2a.PositionTailFullTail

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity Cvs.L2a.CutWeightResidual Cvs.L2a.SpectralMassLevelLeak
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- **L2a on the full tail of the rung span**, given the frame floor, the low mass, the per-level far leak and the
off-diagonal cut bound. -/
theorem L2a_span_fulltail {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (ω ε : ℝ → ℝ) {X T η k₁ t2 εc C κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hT : 2 ≤ T)
    (hlow : ∫ t in {t : ℝ | |t| < T}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ η * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hk₁ : 1 ≤ k₁) (hk₁X : k₁ ≤ X) (hεm : Measurable ε)
    (hε : ∀ k ∈ Icc k₁ X,
      specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k)
          (k * T)
        ≤ ε k * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hω : ContinuousOn ω (Icc 1 X)) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωle : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) (hεc : εc ≤ 1)
    (hNS : cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ εc * (-(cutW ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + C * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol T - 114 / T - (archSymbol T - archSymbol 0) * η
        - (Real.log k₁ + ∫ k in k₁..X, min 1 (2 * √(ε k)) / k) - C - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hΦ := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span a hg hg₁ hg₂c hang X
  have hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex ⌊X⌋₊ ⌊X⌋₊ :=
    fun k hk hkX => Cvs.L2a.PositionTailSpanAdapters.mem_primePowIndex_floor hk hkX
  have hloc := hloc_of_levels (fun ξ => ∑ i, a i * psi c (g i) ξ) ε hX1 hΦ hT hk₁ hk₁X hεm hε
  have hpole := Cvs.L2a.RungSpanPole.pole_span a hg hg₁ hg₂c hang hX hc hχ0 hσ hM hJ hκ hFF
  exact Cvs.L2a.LogPositionCut.L2a_logPos_cut _ ω ⌊X⌋₊ ⌊X⌋₊ hX1 hΦ hPR hT hlow hloc hω ht2' hω0 hωle hωeq hεc
    hNS hpole

end Cvs.L2a.PositionTailFullTail
