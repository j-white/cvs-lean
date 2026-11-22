import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The effective symbol, with the cancellation in one object

    `weilForm P R f = 2 A B + ∫ (archSymbol t − primeSymbol P R t) · specDensity f t dt`

so the near-cancellation between the archimedean and prime sides is one multiplier rather
than a difference of two large integrals.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.EffectiveSymbol

/-- **The prime side's symbol.**  Each prime power contributes a cosine at its own log. -/
def primeSymbol (P R : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
    ∑ r ∈ Finset.Icc 1 R,
      2 * primePowerWeight p r * Real.cos (t * ((r : ℝ) * Real.log p))

/-- **The symmetric pair, from `Cvs.WeilForm.SelfConvolutionCosine`.**  `cos` is even, so the two shifts give the same
cosine integral and the pair is twice it.  No integrability beyond `Cvs.WeilForm.SelfConvolutionCosine`'s own. -/
theorem cos_pair {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) (τ : ℝ) :
    selfConvolution f τ + selfConvolution f (-τ)
      = ∫ t : ℝ, 2 * Real.cos (t * τ) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  have hgint := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hfint
  have hW := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint
  have hcont : Continuous (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf)
  rw [Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hW hcont.continuousAt,
    Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hW hcont.continuousAt]
  have hneg : (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * Real.cos (t * (-τ)))
      = ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * Real.cos (t * τ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [show t * -τ = -(t * τ) from by ring, Real.cos_neg])
  rw [hneg, ← two_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

/-- **The prime side, spectrally.**  `Cvs.WeilForm.SelfConvolutionCosine` puts each `g(r log p)` on the same density the
archimedean side uses; everything else is exchanging two finite sums with the integral. -/
theorem prime_spectral (P R : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    primePowerSideTruncated P R (selfConvolution f)
      = ∫ t : ℝ, primeSymbol P R t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  have hWint := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hint : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∀ r ∈ Finset.Icc 1 R,
      Integrable (fun t : ℝ => 2 * primePowerWeight p r
        * Real.cos (t * ((r : ℝ) * Real.log p))
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) := by
    intro p _ r _
    have hbase : Integrable (fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
        * Real.cos (t * ((r : ℝ) * Real.log p))) (volume : Measure ℝ) := by
      refine hWint.mono' ((hWint.aestronglyMeasurable).mul
        (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)]
      have h1 := Real.abs_cos_le_one (t * ((r : ℝ) * Real.log p))
      have h2 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
      nlinarith
    have := hbase.const_mul (2 * primePowerWeight p r)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    ring
  have hinner : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
      Integrable (fun t : ℝ => ∑ r ∈ Finset.Icc 1 R,
        2 * primePowerWeight p r * Real.cos (t * ((r : ℝ) * Real.log p))
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (volume : Measure ℝ) :=
    fun p hp => integrable_finsetSum _ (fun r hr => hint p hp r hr)
  have hexpand : (∫ t : ℝ, primeSymbol P R t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
          ∑ r ∈ Finset.Icc 1 R, ∫ t : ℝ, 2 * primePowerWeight p r
            * Real.cos (t * ((r : ℝ) * Real.log p))
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
    rw [show (fun t : ℝ => primeSymbol P R t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
        = fun t : ℝ => ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
            ∑ r ∈ Finset.Icc 1 R, 2 * primePowerWeight p r
              * Real.cos (t * ((r : ℝ) * Real.log p))
              * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t from by
      funext t; unfold primeSymbol; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_mul]]
    rw [integral_finsetSum _ hinner]
    exact Finset.sum_congr rfl fun p hp =>
      integral_finsetSum _ (fun r hr => hint p hp r hr)
  rw [hexpand]
  unfold primePowerSideTruncated
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  rw [cos_pair hf hfint ((r : ℝ) * Real.log p), ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

/-! ### The cancellation, as one multiplier -/

/-- **The effective symbol.**  What the archimedean side charges, less what the prime side
refunds. -/
def effSymbol (P R : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - primeSymbol P R t

end Cvs.WeilForm.EffectiveSymbol
