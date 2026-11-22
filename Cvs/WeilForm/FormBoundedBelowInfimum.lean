import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.LevyEnergySublevelBound
import Cvs.WeilForm.Mollify.AeSymmetryEnough
import Cvs.WeilForm.PoleChannelWindowL2
import Cvs.WeilForm.PrimeChannelL2Continuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The form is bounded below on the window, so its infimum exists

    weilForm P R f ≥ archSymbol 0 − (pole bound) − 2·(prime mass)   on the constraint set

the archimedean channel being nonnegative and the other two capped by the unit norm.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.FormBoundedBelowInfimum

variable {L : ℝ}

/-- The lower bound the three channels give. -/
def formFloor (L : ℝ) (P R : ℕ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
    - 2 * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
        * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2)
    - 2 * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R

/-- **The form is bounded below on the constraint set.** -/
theorem formFloor_le (P R : ℕ) {f : ℝ → ℝ} (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    formFloor L P R ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hf
  have hpole := Cvs.WeilForm.LevyEnergySublevelBound.abs_poleTerm_le hmem hsupp hnorm
  have hprime := Cvs.WeilForm.LevyEnergySublevelBound.abs_primeSide_le P R hmem hnorm
  have hg0 : selfConvolution f 0 = 1 := by
    rw [← hnorm, selfConvolution]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  have harch : 0 ≤ ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (1 - selfConvolution f (u / 2)) := by
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    refine mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le ?_
    have hle := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2) hmem
    rw [hg0] at hle
    linarith
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, formFloor, hg0]
  have hp := abs_le.mp hpole
  have hpr := abs_le.mp hprime
  linarith [hp.1, hpr.2, harch]

/-- **And the infimum of the even sector exists.** -/
theorem exists_isGLB_even (hL : 0 < L) (P R : ℕ) :
    ∃ lam, IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R ''
      Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam := by
  refine Real.exists_isGLB ?_ ?_
  · obtain ⟨η, hηmem, hηsymm⟩ := Cvs.WeilForm.Mollify.AeSymmetryEnough.exists_even_member hL
    exact ⟨Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η, ⟨η, ⟨hηmem, hηsymm⟩, rfl⟩⟩
  · refine ⟨formFloor L P R, ?_⟩
    rintro y ⟨f, hf, rfl⟩
    exact formFloor_le P R hf.1

/-- **The even sector's minimiser exists, unconditionally.** -/
theorem exists_even_minimiser (hL : 0 < L) (P R : ℕ) :
    ∃ lam, ∃ g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L,
      IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R ''
        Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam ∧
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam := by
  obtain ⟨lam, hlam⟩ := exists_isGLB_even hL P R
  obtain ⟨g, hg, hgv⟩ := Cvs.WeilForm.EvenBottomAttained.exists_even_minimiser_window hL.le P R hlam
  exact ⟨lam, g, hg, hlam, hgv⟩

end Cvs.WeilForm.FormBoundedBelowInfimum
