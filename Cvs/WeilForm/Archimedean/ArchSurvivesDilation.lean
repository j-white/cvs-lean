import Mathlib
import Cvs.WeilForm.Archimedean.ArchDilationMajorant
import Cvs.WeilForm.Archimedean.DilationOntoDensity
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityDecreasing
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.DilationSelfConvolution
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The archimedean channel survives dilation

    archFull (f (·/a))  →  archFull f     as `a → 1` from the positive side

the dilation having been moved onto the Lévy density by `Cvs.WeilForm.Archimedean.DilationOntoDensity`, where `Cvs.WeilForm.Archimedean.LevyDensityDecreasing` bounds it and
`Cvs.WeilForm.Archimedean.ArchDilationMajorant` says the bound is integrable.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Cvs.Zeta.Explicit.Weil Filter

namespace Cvs.WeilForm.Archimedean.ArchSurvivesDilation

/-- **The dilated channel, with the dilation on the density.** -/
theorem archFull_dilate_eq {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (fun x => f (x / a))
      = a ^ 2 * ∫ w in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w)
          * (selfConvolution f 0 - selfConvolution f (w / 2)) := by
  set D : ℝ → ℝ := fun v => selfConvolution f 0 - selfConvolution f (v / 2) with hD
  have hpt : ∀ u : ℝ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution (fun x => f (x / a)) 0
        - selfConvolution (fun x => f (x / a)) (u / 2))
      = a * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * D (u / a)) := by
    intro u
    rw [Cvs.WeilForm.DilationSelfConvolution.selfConvolution_dilate ha f 0,
      Cvs.WeilForm.DilationSelfConvolution.selfConvolution_dilate ha f (u / 2), zero_div, hD]
    simp only
    have hdiv : u / 2 / a = u / a / 2 := by ring
    rw [hdiv]
    ring
  rw [Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    Cvs.WeilForm.Archimedean.DilationOntoDensity.integral_dilate_onto_density ha D]
  rw [hD]
  ring

/-- **The archimedean channel is continuous under dilation.** -/
theorem tendsto_archFull_dilate {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ)) :
    Filter.Tendsto (fun a : ℝ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (fun x => f (x / a)))
      (nhdsWithin 1 (Set.Ioi 0)) (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f)) := by
  set D : ℝ → ℝ := fun v => selfConvolution f 0 - selfConvolution f (v / 2) with hD
  have hDnn : ∀ w : ℝ, 0 ≤ D w := fun w => by
    have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (w / 2) hf
    rw [hD]; simp only; linarith
  have hcontD : Continuous D := by
    rw [hD]
    exact continuous_const.sub ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).comp
      (continuous_id.div_const 2))
  -- the dominated convergence, with `Cvs.WeilForm.Archimedean.ArchDilationMajorant`'s majorant
  have hmajor := Cvs.WeilForm.Archimedean.ArchDilationMajorant.integrableOn_majorant hf hint
  have hmeas : ∀ᶠ a : ℝ in nhdsWithin 1 (Set.Ioi 0),
      AEStronglyMeasurable (fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) * D w)
        ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    refine Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))) (fun a ha => ?_)
    have hain : (0:ℝ) < a := ha
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ hcontD.continuousOn
    refine Cvs.WeilForm.Archimedean.ArchDilationMajorant.continuousOn_densityU.comp
      (continuous_const.mul continuous_id).continuousOn (fun w hw => ?_)
    simp only [Set.mem_Ioi] at hw ⊢
    positivity
  have hbound : ∀ᶠ a : ℝ in nhdsWithin 1 (Set.Ioi 0),
      ∀ᵐ w : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
        ‖Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) * D w‖
          ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) * D w := by
    refine Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by norm_num : (1:ℝ)/2 < 1))) (fun a ha => ?_)
    have hahalf : (1:ℝ) / 2 ≤ a := le_of_lt ha
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw => ?_)
    have hw0 : (0:ℝ) < w := hw
    have ha0 : (0:ℝ) < a := by linarith
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) :=
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (by positivity)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hDnn w))]
    have hcmp := Cvs.WeilForm.Archimedean.LevyDensityDecreasing.densityU_dilate_le hw0 hahalf
    nlinarith [hDnn w, hcmp]
  have hlim : ∀ᵐ w : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      Filter.Tendsto (fun a : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) * D w)
        (nhdsWithin 1 (Set.Ioi 0)) (nhds (Cvs.WeilForm.Archimedean.LevyDensity.densityU w * D w)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw => ?_)
    have hw0 : (0:ℝ) < w := hw
    have hca : ContinuousAt Cvs.WeilForm.Archimedean.LevyDensity.densityU w :=
      Cvs.WeilForm.Archimedean.ArchDilationMajorant.continuousOn_densityU.continuousAt (Ioi_mem_nhds hw0)
    have hmul : Filter.Tendsto (fun a : ℝ => a * w) (nhdsWithin 1 (Set.Ioi 0)) (nhds w) := by
      have h1 : Filter.Tendsto (fun a : ℝ => a * w) (nhds (1:ℝ)) (nhds (1 * w)) :=
        (Filter.tendsto_id.mul tendsto_const_nhds)
      rw [one_mul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    exact ((hca.tendsto.comp hmul).mul tendsto_const_nhds)
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))
    (l := nhdsWithin 1 (Set.Ioi 0))
    (F := fun a : ℝ => fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * w) * D w)
    (f := fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU w * D w)
    (bound := fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) * D w)
    hmeas hbound hmajor hlim
  -- the prefactor
  have hsq : Filter.Tendsto (fun a : ℝ => a ^ 2) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Filter.Tendsto (fun a : ℝ => a ^ 2) (nhds (1:ℝ)) (nhds ((1:ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 1
    rw [one_pow] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hprod := hsq.mul hDCT
  rw [one_mul] at hprod
  have hgoal : (∫ w in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU w * D w)
      = Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f := rfl
  rw [hgoal] at hprod
  refine hprod.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun a ha => ?_)
  exact (archFull_dilate_eq ha f).symm

end Cvs.WeilForm.Archimedean.ArchSurvivesDilation
