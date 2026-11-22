import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchSymbolUnbounded
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.SpectralTailTransformVariable
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.UnitWindowTransformBounded
import Cvs.Zeta.WeilPositivityStatement

/-!
# Uniform tightness on the form's sublevel set

    ∀ ε > 0, ∃ T > 0, ∀ f,  ∫_{|ξ| > T} ‖𝓕 (cf f) ξ‖² ≤ ε

for every unit window function whose Weil form is bounded — the threshold depends on the
bound and on `ε`, never on the function.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.SublevelUniformTightness

/-- **Uniform tightness.** -/
theorem exists_tight {L B ε : ℝ} (hL : 0 ≤ L) (P R : ℕ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ f : ℝ → ℝ, MemLp f 2 (volume : Measure ℝ) →
      (∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) → (∫ x : ℝ, f x ^ 2) = 1 →
      IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ) →
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f ≤ B →
      (∫ ξ in (Set.Icc (-T) T)ᶜ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) ≤ ε := by
  set K : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      - 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R - 4 * Real.sinh (L / 2) with hK
  set d : ℝ := max 1 ((B - K) / ε) with hd
  have hd1 : (1:ℝ) ≤ d := le_max_left _ _
  have hdpos : 0 < d := lt_of_lt_of_le one_pos hd1
  have hdε : B - K ≤ ε * d := by
    rcases le_or_gt ((B - K) / ε) 1 with h | h
    · have : B - K ≤ ε := by
        rw [div_le_one hε] at h; exact h
      calc B - K ≤ ε := this
        _ = ε * 1 := (mul_one ε).symm
        _ ≤ ε * d := mul_le_mul_of_nonneg_left hd1 hε.le
    · have hde : d = (B - K) / ε := by rw [hd, max_eq_right h.le]
      rw [hde, mul_comm, div_mul_cancel₀ _ hε.ne']
  set c : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + d with hc
  obtain ⟨T0, hT0pos, hT0⟩ := Cvs.WeilForm.Archimedean.ArchSymbolUnbounded.exists_tail_bound c
  refine ⟨T0 / (2 * π), by positivity, ?_⟩
  intro f hf hsupp hnorm hdom hform
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hfint : Integrable f (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf hsupp
  have hzero : selfConvolution f 0 = 1 := by
    rw [Cvs.WeilForm.UnitWindowTransformBounded.selfConvolution_zero, hnorm]
  have hmain := Cvs.WeilForm.TailBoundOnWindow.tailMass_le_window hL P R hf hsupp hdom
    (T := T0) (c := c) (fun t ht => hT0 t ht)
  rw [hzero, mul_one, hc] at hmain
  simp only [add_sub_cancel_left] at hmain
  -- the tail mass is small
  have htail : (∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T0,
      Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) ≤ ε := by
    have h1 : d * (∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T0,
        Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) ≤ B - K := by
      linarith [hmain, hform]
    have h2 : d * (∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T0,
        Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) ≤ ε * d := le_trans h1 hdε
    nlinarith [h2, hdpos]
  -- and it is the transform's tail
  rw [Cvs.WeilForm.SpectralTailTransformVariable.integral_tail_specDensity] at htail
  refine le_trans (setIntegral_mono_set ?_ ?_ ?_) htail
  · exact (Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint).integrableOn
  · exact Filter.Eventually.of_forall fun ξ => sq_nonneg _
  · refine Filter.Eventually.of_forall fun ξ hξ => ?_
    show T0 / (2 * π) ≤ |ξ|
    have hξ' : ¬ (-(T0 / (2 * π)) ≤ ξ ∧ ξ ≤ T0 / (2 * π)) := hξ
    push_neg at hξ'
    rcases le_or_gt ξ 0 with h | h
    · rw [abs_of_nonpos h]
      by_contra hcon
      push_neg at hcon
      exact absurd (hξ' (by linarith)) (by linarith)
    · rw [abs_of_pos h]
      by_contra hcon
      push_neg at hcon
      exact absurd (hξ' (by linarith)) (by linarith)

end Cvs.WeilForm.SublevelUniformTightness
