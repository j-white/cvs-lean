import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormTranslationInvariant
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The constraint set and the form do not see a null set

    f =ᵐ g  ⟹  same self-convolution, same Weil form, and `g` is in the window if `f` is

so every member has a measurable representative with the same form, and no result needs to
assume its members measurable.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormNullSets

variable {L : ℝ}

/-- **The self-convolution is a function of the class.** -/
theorem selfConvolution_congr {f g : ℝ → ℝ} (hfg : f =ᵐ[(volume : Measure ℝ)] g) (u : ℝ) :
    selfConvolution f u = selfConvolution g u := by
  have hshift := ((measurePreserving_add_right (volume : Measure ℝ) u
    ).quasiMeasurePreserving).ae hfg
  refine integral_congr_ae ?_
  filter_upwards [hfg, hshift] with s h1 h2
  rw [h1, h2]

/-- **The Weil form is a function of the class.** -/
theorem weilForm_congr (P R : ℕ) {f g : ℝ → ℝ} (hfg : f =ᵐ[(volume : Measure ℝ)] g) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := by
  have hself : selfConvolution f = selfConvolution g :=
    funext fun u => selfConvolution_congr hfg u
  have hA : (∫ s : ℝ, f s * Real.exp (s / 2)) = ∫ s : ℝ, g s * Real.exp (s / 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with s hs
    rw [hs]
  have hM : (∫ s : ℝ, f s * Real.exp (-(s / 2))) = ∫ s : ℝ, g s * Real.exp (-(s / 2)) := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with s hs
    rw [hs]
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm, Cvs.WeilForm.SelfConvolutionFunctional.weilForm, hself, hA, hM]

/-- **The constraint set is a property of the class, given the support.** -/
theorem mem_windowSet_of_ae {f g : ℝ → ℝ} (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (hfg : f =ᵐ[(volume : Measure ℝ)] g) (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) :
    g ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hf
  refine ⟨hmem.ae_eq hfg, hgs, ?_, ?_⟩
  · rw [← hnorm]
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  · have hlevy_eq : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
      funext u
      rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy,
        selfConvolution_congr hfg 0, selfConvolution_congr hfg (u / 2)]
    rw [hlevy_eq]
    exact hlevy

/-- **Every member has a measurable representative with the same form.** -/
theorem exists_measurable_rep (P R : ℕ) {f : ℝ → ℝ}
    (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    ∃ g ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L, Measurable g ∧
      f =ᵐ[(volume : Measure ℝ)] g ∧
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hf
  set h : ℝ → ℝ := hmem.aestronglyMeasurable.mk f with hh
  set g : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) L) h with hg
  have hhm : Measurable h := hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgm : Measurable g := hhm.indicator measurableSet_Ioc
  have hfh : f =ᵐ[(volume : Measure ℝ)] h := hmem.aestronglyMeasurable.ae_eq_mk
  have hfg : f =ᵐ[(volume : Measure ℝ)] g := by
    filter_upwards [hfh] with x hx
    rw [hg]
    by_cases hmemx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hmemx, hx]
    · rw [Set.indicator_of_notMem hmemx, hsupp x hmemx]
  have hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0 := by
    intro x hx
    rw [hg, Set.indicator_of_notMem hx]
  exact ⟨g, mem_windowSet_of_ae ⟨hmem, hsupp, hnorm, hlevy⟩ hfg hgs, hgm, hfg,
    (weilForm_congr P R hfg).symm⟩

end Cvs.WeilForm.WeilFormNullSets
