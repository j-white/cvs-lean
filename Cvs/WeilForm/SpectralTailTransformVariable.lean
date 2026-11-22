import Mathlib
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The spectral tail, in the transform's own variable

    ∫_{|t| ≥ T} specDensity f t dt = ∫_{|ξ| ≥ T/2π} ‖𝓕 (cf f) ξ‖² dξ

`Cvs.WeilForm.HighFrequencyMassBound` measures the tail in `Cvs.WeilForm.Archimedean.ArchSpectralDensity`'s frequency variable and `Cvs.WeilForm.TransformClassesTotallyBounded` measures it in the
transform's; the two differ by the scaling `t = 2πξ`, whose Jacobian cancels the density's.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Cvs.WeilForm.SpectralTailTransformVariable

/-- **The tail mass, in the transform's variable.** -/
theorem integral_tail_specDensity (T : ℝ) (f : ℝ → ℝ) :
    (∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
      = ∫ ξ in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet (T / (2 * π)),
          ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 := by
  have hpi : (0:ℝ) < 2 * π := by positivity
  set h : ℝ → ℝ := fun ξ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 with hh
  set S : Set ℝ := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet (T / (2 * π)) with hS
  set G : ℝ → ℝ := fun ξ => S.indicator h ξ / (2 * π) with hG
  have hpt : ∀ t : ℝ,
      (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T).indicator (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) t
        = G (t / (2 * π)) := by
    intro t
    have habs : |t / (2 * π)| = |t| / (2 * π) := by
      rw [abs_div, abs_of_pos hpi]
    by_cases ht : t ∈ Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T
    · have hmem : t / (2 * π) ∈ S := by
        rw [hS, Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet, Set.mem_setOf_eq, habs]
        rw [Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet, Set.mem_setOf_eq] at ht
        gcongr
      rw [Set.indicator_of_mem ht, hG]
      simp only
      rw [Set.indicator_of_mem hmem, hh, Cvs.WeilForm.SelfConvolutionCosine.specDensity]
    · have hnmem : t / (2 * π) ∉ S := by
        rw [hS, Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet, Set.mem_setOf_eq, habs]
        rw [Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet, Set.mem_setOf_eq] at ht
        push_neg at ht ⊢
        gcongr
      rw [Set.indicator_of_notMem ht, hG]
      simp only
      rw [Set.indicator_of_notMem hnmem]
      simp
  rw [← integral_indicator (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet T),
    ← integral_indicator (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet (T / (2 * π)))]
  simp only [hpt]
  rw [MeasureTheory.Measure.integral_comp_div G (2 * π), abs_of_pos hpi, hG]
  rw [smul_eq_mul, integral_div]
  field_simp
  rfl

end Cvs.WeilForm.SpectralTailTransformVariable
