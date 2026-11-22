import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailPrimeChannel
import Cvs.L2a.PartOneWeilForm
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
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
# The Weil form of `F_X` converges channel-wise to `W_∞`

`W_∞` is assembled channel by channel from the limits of the pole (Cvs.L2a.FullTailPoleChannel), the `a₀ N` term (Cvs.L2a.FullTailConvergence), the Lévy
integral (Cvs.L2a.FullTailArchChannel) and the prime side (Cvs.L2a.FullTailPrimeChannel); its arch channel is `∫ a(t) ρ_∞(t) dt`. Lower bounds
`κ N_X ≤ W_X` holding frequently pass to `κ N_∞ ≤ W_∞`.
-/

namespace Cvs.L2a.FullTailWeilFormLimit

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.TailLogScaleTest
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- The channel-wise limit of the Weil form: pole, archimedean and prime channels of `F_∞` taken separately. -/
noncomputable def Winf (Φ : ℝ → ℝ) : ℝ :=
  2 * Cvs.L2a.FullTailPoleChannel.piPlus Φ * (∫ θ in Ioi 1, fullTail Φ θ / θ)
    + (archSymbol 0 * (∫ θ in Ioi 1, fullTail Φ θ ^ 2) + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail Φ)))
    - Cvs.L2a.FullTailPrimeChannel.primeInf Φ

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-- The self-convolution at `0` of a log-scale profile is the `θ`-mass `∫_{θ>1} F²`. -/
theorem selfConvolution_logScale_zero (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) 0 = ∫ θ in Ioi 1, F θ ^ 2 := by
  rw [← integral_sq F hF]
  simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, add_zero, sq]

/-- **The Weil form of `F_X` in the `θ` variable**: pole, archimedean and prime channels. -/
theorem weilForm_posTail_eq (Φ : ℝ → ℝ) (X : ℝ) (P R : ℕ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (posTail Φ X))
      = 2 * (∫ θ in Ioi 1, posTail Φ X θ) * (∫ θ in Ioi 1, posTail Φ X θ / θ)
        + (archSymbol 0 * (∫ θ in Ioi 1, posTail Φ X θ ^ 2)
          + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail Φ X)))
        - Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
            (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale (posTail Φ X))) := by
  have hF : ∀ θ ≤ 1, posTail Φ X θ = 0 := fun θ hθ => posTail_zero Φ X hθ
  have e : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (posTail Φ X))
      = 2 * (∫ s, logScale (posTail Φ X) s * exp (s / 2)) * (∫ s, logScale (posTail Φ X) s * exp (-(s / 2)))
        + (archSymbol 0 * Cvs.Zeta.Explicit.Weil.selfConvolution (logScale (posTail Φ X)) 0
          + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail Φ X)))
        - Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
            (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale (posTail Φ X))) := rfl
  rw [e, integral_mul_exp _ hF, integral_mul_exp_neg _ hF, selfConvolution_logScale_zero _ hF]

/-- `F_∞` vanishes at `θ ≤ 1`. -/
theorem fullTail_of_le_one (Φ : ℝ → ℝ) {θ : ℝ} (hθ : θ ≤ 1) : fullTail Φ θ = 0 := by
  simp [fullTail, not_lt.mpr hθ]

/-- **The arch channel of `W_∞` in spectral form**: `a₀ N_∞ + archFull f_∞ = ∫ a(t) ρ_{f_∞}(t) dt`. -/
theorem arch_fullTail_eq_spectral (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    archSymbol 0 * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
        + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c g)))
      = ∫ t, archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale (fullTail (psi c g))) t := by
  obtain ⟨h2, h1⟩ := memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hlevy := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc
  have hsh : ∀ u : ℝ, Integrable (fun s => logScale (fullTail (psi c g)) s
      * logScale (fullTail (psi c g)) (s + u)) volume := fun u =>
    h2.integrable_mul (h2.comp_measurePreserving (measurePreserving_add_right volume u))
  rw [← selfConvolution_logScale_zero _ (fun θ hθ => fullTail_of_le_one _ hθ)]
  exact Cvs.L2a.PartOneWeilForm.arch_eq h2 h1 h2.integrable_sq hsh hlevy
    (Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch h2 h1 hlevy)
    (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1)

/-- **The Weil form of `F_X` converges to `W_∞`** along `P = R = ⌊X⌋`. -/
theorem tendsto_weilForm (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊ (logScale (posTail (psi c g) X))) atTop
      (𝓝 (Winf (psi c g))) := by
  have hlim := ((Cvs.L2a.FullTailPoleChannel.tendsto_pole hg hg₁ hg₂c hc).add
    (((tendsto_N hg hg₁ hg₂c hc).const_mul (archSymbol 0)).add
      (Cvs.L2a.FullTailArchChannel.tendsto_archFull hg hg₁ hg₂c hc))).sub
    (Cvs.L2a.FullTailPrimeChannel.tendsto_primeSide hg hg₁ hg₂c hc)
  refine hlim.congr fun X => ?_
  rw [weilForm_posTail_eq]

/-- **Frequent lower bounds pass to the limit**: `κ N_X ≤ W_X` frequently gives `κ N_∞ ≤ W_∞`. -/
theorem le_Winf_of_frequently (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {κ : ℝ}
    (h : ∃ᶠ X in atTop, κ * (∫ θ in Ioi 1, posTail (psi c g) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊ (logScale (posTail (psi c g) X))) :
    κ * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) ≤ Winf (psi c g) := by
  have hlim := (tendsto_weilForm hg hg₁ hg₂c hc).sub ((tendsto_N hg hg₁ hg₂c hc).const_mul κ)
  have h0 : 0 ≤ Winf (psi c g) - κ * ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2 :=
    ge_of_tendsto_of_frequently hlim (h.mono fun X hX => sub_nonneg.mpr hX)
  linarith

end Cvs.L2a.FullTailWeilFormLimit
