import Mathlib
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The archimedean term against a spectral density

    archSymbol 0 · g 0 + ∫₀^∞ ρ(u)·(g 0 − g (u/2)) du = ∫ W(t)·archSymbol t dt

for `g v = ∫ W(t)·cos(t v) dt`: the continuous form of the mode computation, with the two
integrations exchanged.  Each frequency is charged the symbol at that frequency.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Function

namespace Cvs.WeilForm.Archimedean.ArchSpectralDensity

open Cvs.WeilForm.Archimedean.LevyDensity

/-- The cosine transform is integrable at every displacement, when `W` is. -/
theorem integrable_cos_mul {W : ℝ → ℝ} (hWi : Integrable W) (v : ℝ) :
    Integrable fun t : ℝ => W t * Real.cos (t * v) := by
  refine Integrable.mono' hWi.norm ?_ ?_
  · exact hWi.aestronglyMeasurable.mul
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **The transform's deficit is the Lévy integrand, integrated over the frequencies.** -/
theorem deficit_eq {W g : ℝ → ℝ} (hWi : Integrable W)
    (hg : ∀ v, g v = ∫ t : ℝ, W t * Real.cos (t * v)) (u : ℝ) :
    densityU u * (g 0 - g (u / 2))
      = ∫ t : ℝ, densityU u * ((1 - Real.cos (t / 2 * u)) * W t) := by
  have hg0 : g 0 = ∫ t : ℝ, W t := by
    rw [hg 0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp)
  have hsub : g 0 - g (u / 2) = ∫ t : ℝ, (W t - W t * Real.cos (t * (u / 2))) := by
    rw [hg0, hg (u / 2), integral_sub hWi (integrable_cos_mul hWi (u / 2))]
  rw [hsub, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have hc : Real.cos (t / 2 * u) = Real.cos (t * (u / 2)) := by congr 1; ring
  rw [hc]; ring

/-- **The archimedean term, against a spectral density.**  The interchange is the content:
the position-space Lévy energy is the symbol integrated against the frequencies present. -/
theorem arch_of_spectral {W g : ℝ → ℝ} (hWi : Integrable W)
    (hg : ∀ v, g v = ∫ t : ℝ, W t * Real.cos (t * v))
    (hWA : Integrable fun t : ℝ => W t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
    (hprod : Integrable (uncurry fun u t : ℝ =>
        densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume)) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * g 0
      + (∫ u in Ioi (0:ℝ), densityU u * (g 0 - g (u / 2)))
      = ∫ t : ℝ, W t * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  have hg0 : g 0 = ∫ t : ℝ, W t := by
    rw [hg 0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp)
  -- the inner integral, at a fixed frequency
  have hinner : ∀ t : ℝ, (∫ u in Ioi (0:ℝ), densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
      = W t * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := by
    intro t
    have hre : ∀ u : ℝ, densityU u * ((1 - Real.cos (t / 2 * u)) * W t)
        = W t * Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u := by
      intro u
      unfold Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hre u), integral_const_mul,
      Cvs.WeilForm.Archimedean.ArchTrigonometricData.integral_levyIntegrand]
  have hswap : (∫ u in Ioi (0:ℝ), ∫ t : ℝ,
        densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
      = ∫ t : ℝ, ∫ u in Ioi (0:ℝ), densityU u * ((1 - Real.cos (t / 2 * u)) * W t) :=
    integral_integral_swap hprod
  have hlhs : (∫ u in Ioi (0:ℝ), densityU u * (g 0 - g (u / 2)))
      = ∫ t : ℝ, W t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun u _ => deficit_eq hWi hg u), hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hlhs, hg0, ← integral_const_mul, ← integral_add (hWi.const_mul _) hWA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  ring

end Cvs.WeilForm.Archimedean.ArchSpectralDensity
