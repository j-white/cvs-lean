import Mathlib
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin

/-!
# Frequency truncation in `L²`, and what it leaves behind

    `‖u − cut T u‖² = ∫_{|ξ| ≥ T} ‖𝓕 u ξ‖²`

where `cut T u` keeps the frequencies below `T`: the transform is an isometry, so the
distance to the truncation is the spectral mass on the tail.
-/

noncomputable section

open MeasureTheory FourierTransform

namespace Cvs.Upstream.FrequencyTruncationL2

/-- **Frequency truncation** at level `T`: transform, keep `|ξ| < T`, transform back. -/
def cut (T : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (((Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))).indicator
      (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet T).compl.nullMeasurableSet).toLp _)

/-- The transform of the truncation is the truncated transform. -/
theorem fourier_cut (T : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (𝓕 (cut T u) : Lp ℂ 2 (volume : Measure ℝ))
      = ((Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))).indicator
          (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet T).compl.nullMeasurableSet).toLp _ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

/-- **The distance to the truncation is the spectral mass on the tail.** -/
theorem norm_sub_cut_sq (T : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u - cut T u‖ ^ 2
      = ∫ ξ in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T,
          ‖((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 u with hF
  set S := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T with hS
  have hSm : MeasurableSet S := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet T
  -- the transform is an isometry
  have hiso : ‖u - cut T u‖ = ‖F - 𝓕 (cut T u)‖ := by
    rw [← (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map (u - cut T u), map_sub]
    rfl
  rw [hiso, fourier_cut, Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral]
  -- pointwise, `F − 1_{Sᶜ} F = 1_S F`
  have hae : (fun x => ‖((F - ((Lp.memLp F).indicator hSm.compl.nullMeasurableSet).toLp _ :
      Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2)
      =ᵐ[volume] fun x => S.indicator (fun x => ‖(F : ℝ → ℂ) x‖ ^ 2) x := by
    filter_upwards [Lp.coeFn_sub F (((Lp.memLp F).indicator hSm.compl.nullMeasurableSet).toLp _),
      ((Lp.memLp F).indicator hSm.compl.nullMeasurableSet).coeFn_toLp] with x hsub hind
    rw [hsub, Pi.sub_apply, hind]
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx]
  rw [integral_congr_ae hae, integral_indicator hSm]

end Cvs.Upstream.FrequencyTruncationL2
