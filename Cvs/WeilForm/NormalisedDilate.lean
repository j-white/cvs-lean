import Mathlib
import Cvs.WeilForm.Archimedean.ArchDilationMajorant
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityDecreasing
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.DilationSelfConvolution
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.WeilFormDilationContinuous
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The normalised dilate lies in the dilated window's constraint set

    a⁻¹ᐟ² · f (·/a)  ∈  windowSet (a·L)     for `1/2 ≤ a ≤ 1` and `f ∈ windowSet L`

and its Weil form is `a⁻¹` times the dilate's, so the whole first stage stays inside the
constraint the compactness argument is stated over.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.NormalisedDilate

/-- **A dilate of an `L²` function is `L²`.** -/
theorem memLp_dilate {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun x => f (x / a)) 2 (volume : Measure ℝ) := by
  have hqmp : QuasiMeasurePreserving (fun x : ℝ => x / a)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    refine ⟨(measurable_id.div_const a).aemeasurable, ?_⟩
    have hfun : (fun x : ℝ => x / a) = fun x : ℝ => a⁻¹ * x := by
      funext x; rw [div_eq_inv_mul]
    rw [hfun, Real.map_volume_mul_left (inv_ne_zero ha.ne')]
    exact Measure.smul_absolutelyContinuous
  have hmeasA : AEStronglyMeasurable (fun x : ℝ => f (x / a)) (volume : Measure ℝ) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  refine (memLp_two_iff_integrable_sq hmeasA).mpr ?_
  exact (hf.integrable_sq).comp_div ha.ne'

/-- **The dilation-shifted density pairs integrably with the deficit.** -/
theorem integrableOn_densityU_dilate {a : ℝ} (ha : 1/2 ≤ a) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn (fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w)
      * (selfConvolution f 0 - selfConvolution f (w / 2))) (Set.Ioi 0) (volume : Measure ℝ) := by
  have ha0 : (0:ℝ) < a := by linarith
  set D : ℝ → ℝ := fun v => selfConvolution f 0 - selfConvolution f (v / 2) with hD
  have hDnn : ∀ w : ℝ, 0 ≤ D w := fun w => by
    have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (w / 2) hf
    rw [hD]; simp only; linarith
  have hcontD : Continuous D := by
    rw [hD]
    exact continuous_const.sub ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).comp
      (continuous_id.div_const 2))
  have hmajor := Cvs.WeilForm.Archimedean.ArchDilationMajorant.integrableOn_majorant hf hint
  refine Integrable.mono' hmajor ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ hcontD.continuousOn
    refine Cvs.WeilForm.Archimedean.ArchDilationMajorant.continuousOn_densityU.comp
      (continuous_const.mul continuous_id).continuousOn (fun w hw => ?_)
    simp only [Set.mem_Ioi] at hw ⊢
    positivity
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw => ?_)
    have hw0 : (0:ℝ) < w := hw
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) :=
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (by positivity)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hDnn w))]
    nlinarith [hDnn w, Cvs.WeilForm.Archimedean.LevyDensityDecreasing.densityU_dilate_le hw0 ha]

/-- **The dilate's Lévy integral converges.** -/
theorem integrableOn_levy_dilate {a : ℝ} (ha : 1/2 ≤ a) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f (x / a))) (Set.Ioi 0)
      (volume : Measure ℝ) := by
  have ha0 : (0:ℝ) < a := by linarith
  set D : ℝ → ℝ := fun v => selfConvolution f 0 - selfConvolution f (v / 2) with hD
  set G : ℝ → ℝ := fun w => Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) * D w with hG
  have hGint : IntegrableOn G (Set.Ioi 0) (volume : Measure ℝ) :=
    integrableOn_densityU_dilate ha hf hint
  have hcomp : IntegrableOn (fun u : ℝ => G (u / a)) (Set.Ioi 0) (volume : Measure ℝ) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff G (0:ℝ) (inv_pos.mpr ha0)).mpr
      (by rwa [mul_zero])
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [div_eq_inv_mul]
  have hpt : ∀ u : ℝ, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f (x / a)) u = a * G (u / a) := by
    intro u
    rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.DilationSelfConvolution.selfConvolution_dilate ha0 f 0,
      Cvs.WeilForm.DilationSelfConvolution.selfConvolution_dilate ha0 f (u / 2), zero_div, hG, hD]
    simp only
    have hdiv : u / 2 / a = u / a / 2 := by ring
    have hcancel : a * (u / a) = u := by field_simp
    rw [hdiv, hcancel]
    ring
  refine (hcomp.const_mul a).congr (Filter.Eventually.of_forall fun u => ?_)
  exact (hpt u).symm

/-- **The normalised dilate lies in the dilated window's constraint set.** -/
theorem mem_windowSet_dilate {L a : ℝ} (ha : 1/2 ≤ a) {f : ℝ → ℝ}
    (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    (fun x => (Real.sqrt a)⁻¹ * f (x / a)) ∈ Cvs.WeilForm.WindowConstraintSet.windowSet (a * L) := by
  have ha0 : (0:ℝ) < a := by linarith
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hf
  have hsq : (Real.sqrt a)⁻¹ ^ 2 = a⁻¹ := by
    rw [inv_pow, Real.sq_sqrt ha0.le]
  refine ⟨(memLp_dilate ha0 hmem).const_mul _, ?_, ?_, ?_⟩
  · intro s hs
    simp only
    rw [Cvs.WeilForm.WeilFormDilationContinuous.support_dilate ha0 hsupp s hs, mul_zero]
  · have hdil := Cvs.WeilForm.DilationSelfConvolution.integral_sq_dilate ha0 f
    have hexp : ∀ x : ℝ, ((Real.sqrt a)⁻¹ * f (x / a)) ^ 2
        = (Real.sqrt a)⁻¹ ^ 2 * f (x / a) ^ 2 := fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul, hdil, hsq,
      hnorm]
    field_simp
  · have hs := Cvs.WeilForm.WeilFormHomogeneous.selfConvolution_smul ((Real.sqrt a)⁻¹) (fun x => f (x / a))
    have hpt : ∀ u : ℝ, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => (Real.sqrt a)⁻¹ * f (x / a)) u
        = (Real.sqrt a)⁻¹ ^ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f (x / a)) u := by
      intro u
      rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, hs, hs]
      ring
    refine ((integrableOn_levy_dilate ha hmem hlevy).const_mul
      ((Real.sqrt a)⁻¹ ^ 2)).congr (Filter.Eventually.of_forall fun u => ?_)
    exact (hpt u).symm

end Cvs.WeilForm.NormalisedDilate
