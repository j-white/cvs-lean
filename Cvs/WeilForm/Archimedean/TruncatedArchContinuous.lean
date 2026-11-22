import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The arch channel, truncated away from the origin, is L²-continuous

    |archTrunc δ f − archTrunc δ h| ≤ 2·‖f−h‖₂(‖f‖₂+‖h‖₂)·∫_{u>δ} densityU

`Cvs.WeilForm.SelfConvolutionL2Continuous`'s bound is uniform in the shift, so the whole truncated Lévy integral moves by at
most that bound times the mass of the density, which `Cvs.WeilForm.Archimedean.LevyDensityIntegrable` makes finite.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.TruncatedArchContinuous

/-- **The self-convolution is bounded by the energy.** -/
theorem abs_selfConvolution_le {f : ℝ → ℝ} (u : ℝ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    |selfConvolution f u| ≤ ∫ x : ℝ, f x ^ 2 := by
  have hfu : MemLp (fun s => f (s + u)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hfu
  have htr : (∫ s : ℝ, f (s + u) ^ 2) = ∫ s : ℝ, f s ^ 2 :=
    integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun s : ℝ => f s ^ 2) u
  rw [htr] at hcs
  have hnn : 0 ≤ ∫ x : ℝ, f x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  rwa [Real.mul_self_sqrt hnn] at hcs

/-- The Lévy integral, cut off below `δ`. -/
def archTrunc (δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Ioi δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))

/-- Each truncated integrand is integrable, being dominated by a multiple of the density. -/
theorem integrableOn_archTrunc {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ)) :
    IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi δ) (volume : Measure ℝ) := by
  set E : ℝ := ∫ x : ℝ, f x ^ 2 with hE
  have hdom : Integrable (fun u : ℝ => (2 * E) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      ((volume : Measure ℝ).restrict (Set.Ioi δ)) :=
    (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU hδ).const_mul (2 * E)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2)))
      ((volume : Measure ℝ).restrict (Set.Ioi δ)) := by
    have hd : ContinuousOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi δ) := by
      apply ContinuousOn.div
      · exact (Real.continuous_exp.comp (continuous_id.div_const 4).neg).continuousOn
      · exact (continuous_const.sub (Real.continuous_exp.comp continuous_id.neg)).continuousOn
      · intro u hu
        have hu0 : (0:ℝ) < u := lt_trans hδ hu
        have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        exact (sub_pos.mpr this).ne'
    have hq : QuasiMeasurePreserving (fun u : ℝ => (2⁻¹ : ℝ) • u)
        (volume : Measure ℝ) (volume : Measure ℝ) :=
      Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (r := (2⁻¹ : ℝ))
        (by norm_num)
    have hhalf : AEStronglyMeasurable (fun u : ℝ => selfConvolution f (u / 2))
        (volume : Measure ℝ) := by
      have h := hfc.comp_quasiMeasurePreserving hq
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp [smul_eq_mul, div_eq_inv_mul]
    exact ((hd.aestronglyMeasurable measurableSet_Ioi).mul
      ((aestronglyMeasurable_const.sub hhalf).restrict))
  refine hdom.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  have hu0 : (0:ℝ) < u := lt_trans hδ hu
  have hpos : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
  have hb0 := abs_selfConvolution_le (f := f) 0 hf
  have hbu := abs_selfConvolution_le (f := f) (u / 2) hf
  have hsub : |selfConvolution f 0 - selfConvolution f (u / 2)| ≤ 2 * E := by
    calc |selfConvolution f 0 - selfConvolution f (u / 2)|
        ≤ |selfConvolution f 0| + |selfConvolution f (u / 2)| := abs_sub _ _
      _ ≤ E + E := add_le_add hb0 hbu
      _ = 2 * E := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * |selfConvolution f 0 - selfConvolution f (u / 2)|
      ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (2 * E) := by
        exact mul_le_mul_of_nonneg_left hsub hpos.le
    _ = (2 * E) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by ring

/-- **The truncated arch channel is `L²`-continuous.** -/
theorem abs_archTrunc_sub_le {δ : ℝ} (hδ : 0 < δ) {f h : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ))
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hhc : AEStronglyMeasurable (selfConvolution h) (volume : Measure ℝ)) :
    |archTrunc δ f - archTrunc δ h|
      ≤ 2 * (Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
            * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)))
          * ∫ u in Set.Ioi δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  set K : ℝ := Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
      * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; positivity
  have hIf := integrableOn_archTrunc hδ hf hfc
  have hIh := integrableOn_archTrunc hδ hh hhc
  have hDens := Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU hδ
  have hbig : Integrable (fun u : ℝ => (2 * K) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      ((volume : Measure ℝ).restrict (Set.Ioi δ)) := hDens.const_mul (2 * K)
  -- pointwise
  have hpt : ∀ u ∈ Set.Ioi δ,
      ‖Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution f 0 - selfConvolution f (u / 2))
        - Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution h 0 - selfConvolution h (u / 2))‖
        ≤ (2 * K) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    intro u hu
    have hu0 : (0:ℝ) < u := lt_trans hδ hu
    have hpos : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    have hb0 := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := f) (h := h) 0 hf hh
    have hbu := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := f) (h := h) (u / 2) hf hh
    have hcomb : |(selfConvolution f 0 - selfConvolution f (u / 2))
        - (selfConvolution h 0 - selfConvolution h (u / 2))| ≤ 2 * K := by
      have hrw : (selfConvolution f 0 - selfConvolution f (u / 2))
          - (selfConvolution h 0 - selfConvolution h (u / 2))
          = (selfConvolution f 0 - selfConvolution h 0)
            - (selfConvolution f (u / 2) - selfConvolution h (u / 2)) := by ring
      rw [hrw]
      calc |(selfConvolution f 0 - selfConvolution h 0)
              - (selfConvolution f (u / 2) - selfConvolution h (u / 2))|
          ≤ |selfConvolution f 0 - selfConvolution h 0|
              + |selfConvolution f (u / 2) - selfConvolution h (u / 2)| := abs_sub _ _
        _ ≤ K + K := add_le_add hb0 hbu
        _ = 2 * K := by ring
    have hfactor : Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2))
        - Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution h 0 - selfConvolution h (u / 2))
        = Cvs.WeilForm.Archimedean.LevyDensity.densityU u
            * ((selfConvolution f 0 - selfConvolution f (u / 2))
              - (selfConvolution h 0 - selfConvolution h (u / 2))) := by ring
    rw [hfactor, Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * |(selfConvolution f 0 - selfConvolution f (u / 2))
              - (selfConvolution h 0 - selfConvolution h (u / 2))|
        ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (2 * K) := mul_le_mul_of_nonneg_left hcomb hpos.le
      _ = (2 * K) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by ring
  have hstep : |archTrunc δ f - archTrunc δ h|
      ≤ ∫ u in Set.Ioi δ, (2 * K) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    rw [archTrunc, archTrunc, ← integral_sub hIf hIh]
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine integral_mono_ae ((hIf.sub hIh).abs) hbig ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hstep
  linarith [hstep]

end Cvs.WeilForm.Archimedean.TruncatedArchContinuous
