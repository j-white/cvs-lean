import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form does not see a translation

    weilForm P R (f (·+c)) = weilForm P R f

The self-convolution is translation invariant, and the two pole integrals pick up reciprocal
exponentials whose product is one.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormTranslationInvariant

/-- **The translate is supported in the translated window.**  For `c < 0` the left endpoint
moves off the origin, which is the room a mollification needs. -/
theorem support_translate {L c : ℝ} {f : ℝ → ℝ}
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) :
    ∀ s ∉ Set.Ioc (-c) (L - c), f (s + c) = 0 := by
  intro s hs
  refine hsupp (s + c) ?_
  intro hmem
  simp only [Set.mem_Ioc] at hmem
  exact hs (Set.mem_Ioc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)

/-- **The translate lies in the translated window's constraint set.** -/
theorem mem_windowSet_translate {L c : ℝ} (hc : c ≤ 0) {f : ℝ → ℝ}
    (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    (fun x => f (x + c)) ∈ Cvs.WeilForm.WindowConstraintSet.windowSet (L - c) := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hf
  refine ⟨hmem.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) c),
    ?_, ?_, ?_⟩
  · intro s hs
    refine support_translate hsupp s ?_
    intro hmem'
    simp only [Set.mem_Ioc] at hmem'
    exact hs (Set.mem_Ioc.mpr ⟨by linarith [hmem'.1], hmem'.2⟩)
  · rw [Cvs.WeilForm.CentredWindowTranslate.integral_sq_translate f c]
    exact hnorm
  · have hlevy_eq : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f (x + c))
        = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
      funext u
      rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy,
        Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f c 0,
        Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f c (u / 2)]
    rw [hlevy_eq]
    exact hlevy

end Cvs.WeilForm.WeilFormTranslationInvariant
