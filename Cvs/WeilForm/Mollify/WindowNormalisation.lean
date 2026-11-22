import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# Normalising an element of the window

    `(∫h²)^{−1/2}·h ∈ windowSet L`, for `h` in the window with positive energy

and the energy of an `L²`-convergent sequence converges, which makes the factor tend to one.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Mollify.WindowNormalisation

/-- **Normalising lands in the constraint set.** -/
theorem mem_windowSet_normalised {L : ℝ} {h : ℝ → ℝ} (hmem : MemLp h 2 (volume : Measure ℝ))
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, h s = 0)
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy h) (Set.Ioi 0) (volume : Measure ℝ))
    (hpos : 0 < ∫ x : ℝ, h x ^ 2) :
    (fun x => (Real.sqrt (∫ y : ℝ, h y ^ 2))⁻¹ * h x) ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
  set E : ℝ := ∫ y : ℝ, h y ^ 2 with hE
  have hsq : (Real.sqrt E)⁻¹ ^ 2 = E⁻¹ := by rw [inv_pow, Real.sq_sqrt hpos.le]
  refine ⟨hmem.const_mul _, ?_, ?_, ?_⟩
  · intro s hs
    simp only
    rw [hsupp s hs, mul_zero]
  · have hexp : ∀ x : ℝ, ((Real.sqrt E)⁻¹ * h x) ^ 2 = (Real.sqrt E)⁻¹ ^ 2 * h x ^ 2 :=
      fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul, hsq, ← hE]
    field_simp
  · have hpt : ∀ u : ℝ, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => (Real.sqrt E)⁻¹ * h x) u
        = (Real.sqrt E)⁻¹ ^ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy h u := by
      intro u
      rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy,
        Cvs.WeilForm.WeilFormHomogeneous.selfConvolution_smul, Cvs.WeilForm.WeilFormHomogeneous.selfConvolution_smul]
      ring
    refine (hlevy.const_mul ((Real.sqrt E)⁻¹ ^ 2)).congr
      (Filter.Eventually.of_forall fun u => ?_)
    exact (hpt u).symm

/-- **Normalising scales the form by the reciprocal of the energy.** -/
theorem weilForm_normalised (P R : ℕ) {E : ℝ} (hE : 0 < E) (h : ℝ → ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun x => (Real.sqrt E)⁻¹ * h x)
      = E⁻¹ * Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R h := by
  rw [Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul, inv_pow, Real.sq_sqrt hE.le]

/-- **The energy of an `L²`-convergent sequence converges.** -/
theorem tendsto_integral_sq {C : ℝ} {g : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hconv : Tendsto (fun n : ℕ => ∫ x : ℝ, (F n x - g x) ^ 2) atTop (nhds 0))
    (hbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ C) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, F n x ^ 2) atTop (nhds (∫ x : ℝ, g x ^ 2)) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ, (F n x - g x) ^ 2) with hs
  set B : ℝ := Real.sqrt C + Real.sqrt (∫ x : ℝ, g x ^ 2) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hstend : Tendsto s atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [hs, Real.sqrt_zero, Function.comp_def] using this
  have hMtend : Tendsto (fun n => s n * B) atTop (nhds 0) := by
    have := hstend.mul_const B
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hMtend ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hkey := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := F n) (h := g) 0 (hF n) hg
  have hg0F : selfConvolution (F n) 0 = ∫ x : ℝ, F n x ^ 2 := by
    rw [selfConvolution]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  have hg0g : selfConvolution g 0 = ∫ x : ℝ, g x ^ 2 := by
    rw [selfConvolution]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  rw [hg0F, hg0g] at hkey
  have hEn : Real.sqrt (∫ x : ℝ, F n x ^ 2) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbdd n)
  have hle : s n * (Real.sqrt (∫ x : ℝ, F n x ^ 2)
      + Real.sqrt (∫ x : ℝ, g x ^ 2)) ≤ s n * B := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [hB]; linarith
  have hdN := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ s n * B)] at hdN
  rw [Real.dist_eq]
  linarith [hkey, hle, hdN]

end Cvs.WeilForm.Mollify.WindowNormalisation
