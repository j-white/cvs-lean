import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The effective symbol, from three facts about the window

    `MemLp f 2`,  `Integrable f`,  `IntegrableOn (levy f) (Ioi 0)`
      ⟹  `weilForm P R f = 2 A B + ∫ effSymbol P R t · specDensity f t dt`

every other side condition being derivable from those.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.EffectiveSymbolThreeFacts

/-- **The symbol against the density is integrable.**  `Cvs.WeilForm.Archimedean.LevyTonelli` gives it for `archSymbol` less
its value at the origin; adding back a multiple of the density gives the symbol itself. -/
theorem integrable_arch_mul {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ))
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    Integrable (fun t : ℝ => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) := by
  have h1 := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf hfint hdom
  have h2 := (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint).const_mul
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

/-- **The prime symbol against the density is integrable.**  A finite sum of bounded cosines
against an integrable density. -/
theorem integrable_prime_mul (P R : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    Integrable (fun t : ℝ => Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) := by
  have hW := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hone : ∀ τ : ℝ, Integrable (fun t : ℝ =>
      Real.cos (t * τ) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) := by
    intro τ
    refine hW.mono' (((Real.continuous_cos.comp
      (continuous_id.mul continuous_const)).aestronglyMeasurable).mul
        hW.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)]
    have h1 := Real.abs_cos_le_one (t * τ)
    have h2 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
    nlinarith
  have hterm : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime, Integrable
      (fun t : ℝ => ∑ r ∈ Finset.Icc 1 R, 2 * primePowerWeight p r
        * Real.cos (t * ((r : ℝ) * Real.log p))
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) := by
    intro p _
    refine integrable_finsetSum _ fun r _ => ?_
    refine ((hone ((r : ℝ) * Real.log p)).const_mul
      (2 * primePowerWeight p r)).congr (Filter.Eventually.of_forall fun t => ?_)
    ring
  refine (integrable_finsetSum _ hterm).congr (Filter.Eventually.of_forall fun t => ?_)
  unfold Cvs.WeilForm.EffectiveSymbol.primeSymbol
  simp only [Finset.sum_mul]

/-! ### The identity, with nothing left to supply -/

end Cvs.WeilForm.EffectiveSymbolThreeFacts
