import Mathlib
import Cvs.Upstream.L2DilationContinuity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchSurvivesDilation
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ComposedApproximantL2
import Cvs.WeilForm.Mollify.MollifiedFormConverges
import Cvs.WeilForm.NormalisedDilate
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WeilFormTranslationInvariant
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The dilate-and-translate, in the window and with a convergent channel

    `shifted L η n ∈ windowSet L`,  and  `archFull (shifted L η n) → archFull η`

the dilation being homogeneous of degree two and the translation exact.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil Cvs.Upstream.L2DilationContinuity

namespace Cvs.WeilForm.Mollify.DilateTranslate

variable {L : ℝ} {η : ℝ → ℝ}

/-- **The dilate-and-translate is in the window.** -/
theorem mem_windowSet_shifted (hL : 0 < L) (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (n : ℕ) : Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
  have hdil : dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila n) η
      ∈ Cvs.WeilForm.WindowConstraintSet.windowSet (Cvs.WeilForm.Mollify.ComposedApproximant.dila n * L) :=
    Cvs.WeilForm.NormalisedDilate.mem_windowSet_dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila_half_le n) hη
  have htr := Cvs.WeilForm.WeilFormTranslationInvariant.mem_windowSet_translate
    (c := -(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n))
    (by linarith [Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n]) hdil
  refine Cvs.WeilForm.Mollify.MollifiedFormConverges.windowSet_mono ?_ htr
  have := Cvs.WeilForm.Mollify.ComposedApproximant.fit L n
  have := Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n
  linarith

/-- **The archimedean channel is homogeneous of degree two under the normalisation.** -/
theorem archFull_shifted_eq (n : ℕ) (L : ℝ) (η : ℝ → ℝ) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n)
      = (Cvs.WeilForm.Mollify.ComposedApproximant.dila n)⁻¹
        * Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
            (fun x => η (x / Cvs.WeilForm.Mollify.ComposedApproximant.dila n)) := by
  set a : ℝ := Cvs.WeilForm.Mollify.ComposedApproximant.dila n with ha
  have hapos : 0 < a := Cvs.WeilForm.Mollify.ComposedApproximant.dila_pos n
  have hsq : (Real.sqrt a)⁻¹ ^ 2 = a⁻¹ := by rw [inv_pow, Real.sq_sqrt hapos.le]
  have hself : ∀ u : ℝ, selfConvolution (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n) u
      = a⁻¹ * selfConvolution (fun x => η (x / a)) u := by
    intro u
    have htr : selfConvolution (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n) u
        = selfConvolution (dilate a η) u :=
      Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate (dilate a η)
        (-(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n)) u
    have hd : dilate a η = fun x => (Real.sqrt a)⁻¹ * η (x / a) := rfl
    rw [htr, hd, Cvs.WeilForm.WeilFormHomogeneous.selfConvolution_smul, hsq]
  rw [Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [hself 0, hself (u / 2)]
  ring

/-- **The dilate-and-translate's archimedean channel converges.** -/
theorem tendsto_archFull_shifted (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) (L' : ℝ) :
    Filter.Tendsto (fun n : ℕ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
      (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L' η n)) Filter.atTop
      (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull η)) := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hη
  have hbase := Cvs.WeilForm.Archimedean.ArchSurvivesDilation.tendsto_archFull_dilate hmem hlevy
  have hcomp := hbase.comp Cvs.WeilForm.Mollify.ComposedApproximantL2.tendsto_dila_within
  have hinv : Filter.Tendsto (fun n : ℕ => (Cvs.WeilForm.Mollify.ComposedApproximant.dila n)⁻¹)
      Filter.atTop (nhds 1) := by
    have h1 := Cvs.WeilForm.Mollify.ComposedApproximant.tendsto_dila.inv₀ one_ne_zero
    rw [inv_one] at h1
    exact h1
  have hprod := hinv.mul hcomp
  rw [one_mul] at hprod
  refine hprod.congr (fun n => ?_)
  exact (archFull_shifted_eq n L' η).symm

end Cvs.WeilForm.Mollify.DilateTranslate
