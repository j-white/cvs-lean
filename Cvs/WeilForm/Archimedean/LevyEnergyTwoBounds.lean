import Mathlib
import Cvs.Upstream.LevyConditionL1Modulus
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyEnergyResolvent
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Two bounds on the Lévy energy

For `f, g ∈ L²` with integrable Lévy integrands and `λ > 0`:
`archFull(f + g) ≤ (1 + λ) archFull g + (1 + 1/λ) archFull f`. For `|f| ≤ H` with `∫|f − f(· + v)| ≤ Lv` and
`0 < u₀ ≤ 1`: `archFull f ≤ HLu₀ + 4N log(1/u₀) + 16N`, `N = ∫ f²`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Zeta.Explicit.Weil (selfConvolution)

namespace Cvs.WeilForm.Archimedean.LevyEnergyTwoBounds

/-- **The Lévy energy of a bounded function with a linear modulus**:
`archFull f ≤ HLu₀ + 4N log(1/u₀) + 16N` for `0 < u₀ ≤ 1`, `N = ∫ f²`. -/
theorem archFull_le_of_modulus {f : ℝ → ℝ} (hf : MemLp f 2 volume) {H L u₀ : ℝ} (hH : ∀ s, |f s| ≤ H)
    (hdi : ∀ v, 0 ≤ v → Integrable (fun s => f s - f (s + v)) volume)
    (hmod : ∀ v, 0 ≤ v → ∫ s, |f s - f (s + v)| ≤ L * v) (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
      ≤ H * L * u₀ + 4 * (∫ s, f s ^ 2) * Real.log (1 / u₀) + 16 * (∫ s, f s ^ 2) := by
  set N := ∫ s, f s ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun s => sq_nonneg _
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  have hL0 : 0 ≤ L := by
    have h := hmod 1 zero_le_one
    have : 0 ≤ ∫ s, |f s - f (s + 1)| := integral_nonneg fun s => abs_nonneg _
    linarith
  have hlevy := Cvs.Upstream.LevyConditionL1Modulus.integrableOn_levy hf hH hdi hmod
  -- the two pointwise bounds on the increment
  have hinc : ∀ v, 0 ≤ v → selfConvolution f 0 - selfConvolution f v ≤ H * L * v := by
    intro v hv
    rw [Cvs.Upstream.LevyConditionL1Modulus.selfConvolution_sub hf]
    have hint : Integrable (fun s => f s * (f s - f (s + v))) volume :=
      (hdi v hv).bdd_mul (c := H) hf.aestronglyMeasurable (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact hH s)
    calc ∫ s, f s * (f s - f (s + v)) ≤ ∫ s, H * |f s - f (s + v)| := by
          refine integral_mono hint ((hdi v hv).abs.const_mul H) fun s => ?_
          calc f s * (f s - f (s + v)) ≤ |f s * (f s - f (s + v))| := le_abs_self _
            _ = |f s| * |f s - f (s + v)| := abs_mul _ _
            _ ≤ H * |f s - f (s + v)| := mul_le_mul_of_nonneg_right (hH s) (abs_nonneg _)
      _ = H * ∫ s, |f s - f (s + v)| := integral_const_mul _ _
      _ ≤ H * (L * v) := mul_le_mul_of_nonneg_left (hmod v hv) hH0
      _ = H * L * v := by ring
  have hbd : ∀ v, selfConvolution f 0 - selfConvolution f v ≤ 2 * N := by
    intro v
    have h1 := Cvs.WeilForm.Archimedean.LevyEnergyResolvent.abs_selfConvolution_le hf v
    have h0 : selfConvolution f 0 = N := by
      rw [hN]; unfold selfConvolution; congr 1; funext s; rw [add_zero]; ring
    have := (abs_le.mp h1).1
    linarith
  -- the majorant
  set g : ℝ → ℝ := fun u => (Ioc 0 u₀).indicator (fun _ => H * L) u + (Ioc u₀ 1).indicator (fun u => 4 * N / u) u
    + (Ioi 1).indicator (fun u => 4 * N * exp (-(1 / 4) * u)) u with hg
  have hpt : ∀ u ∈ Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u ≤ g u := by
    intro u hu
    have hu0 : 0 < u := hu
    have hd := Cvs.WeilForm.Archimedean.LevyMeasure.densityU_le hu0
    have hdp := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    have he : exp (-(u / 4)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    have hS0 : 0 ≤ selfConvolution f 0 - selfConvolution f (u / 2) := by
      have := (abs_le.mp (Cvs.WeilForm.Archimedean.LevyEnergyResolvent.abs_selfConvolution_le hf (u / 2))).2; linarith
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    have n1 : 0 ≤ (Ioc 0 u₀).indicator (fun _ => H * L) u := indicator_nonneg (fun _ _ => by positivity) u
    have n2 : 0 ≤ (Ioc u₀ 1).indicator (fun u => 4 * N / u) u :=
      indicator_nonneg (fun x hx => by have : 0 < x := lt_trans hu₀ hx.1; positivity) u
    have n3 : 0 ≤ (Ioi 1).indicator (fun u => 4 * N * exp (-(1 / 4) * u)) u := indicator_nonneg (fun _ _ => by positivity) u
    rcases le_or_gt u u₀ with h1 | h1
    · have hmem : u ∈ Ioc 0 u₀ := ⟨hu0, h1⟩
      have h2 : selfConvolution f 0 - selfConvolution f (u / 2) ≤ H * L * (u / 2) := hinc _ (by linarith)
      calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution f 0 - selfConvolution f (u / 2))
          ≤ (1 + u) * exp (-(u / 4)) / u * (H * L * (u / 2)) := mul_le_mul hd h2 hS0 (by positivity)
        _ = (1 + u) * exp (-(u / 4)) * (H * L) / 2 := by field_simp
        _ ≤ 2 * 1 * (H * L) / 2 := by gcongr; linarith
        _ = (Ioc 0 u₀).indicator (fun _ => H * L) u := by rw [indicator_of_mem hmem]; ring
        _ ≤ g u := by simp only [hg]; linarith
    rcases le_or_gt u 1 with h2 | h2
    · have hmem : u ∈ Ioc u₀ 1 := ⟨h1, h2⟩
      calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution f 0 - selfConvolution f (u / 2))
          ≤ (1 + u) * exp (-(u / 4)) / u * (2 * N) := mul_le_mul hd (hbd _) hS0 (by positivity)
        _ ≤ 2 * 1 / u * (2 * N) := by gcongr; linarith
        _ = (Ioc u₀ 1).indicator (fun u => 4 * N / u) u := by rw [indicator_of_mem hmem]; field_simp; ring
        _ ≤ g u := by simp only [hg]; linarith
    · have hmem : u ∈ Ioi (1 : ℝ) := h2
      calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution f 0 - selfConvolution f (u / 2))
          ≤ (1 + u) * exp (-(u / 4)) / u * (2 * N) := mul_le_mul hd (hbd _) hS0 (by positivity)
        _ ≤ 2 * exp (-(u / 4)) * (2 * N) := by
            gcongr
            rw [div_le_iff₀ hu0]
            nlinarith [exp_pos (-(u / 4))]
        _ = (Ioi 1).indicator (fun u => 4 * N * exp (-(1 / 4) * u)) u := by
            rw [indicator_of_mem hmem, show -(1 / 4) * u = -(u / 4) by ring]; ring
        _ ≤ g u := by simp only [hg]; linarith
  -- integrating the majorant
  have i1 : Integrable ((Ioc 0 u₀).indicator (fun _ : ℝ => H * L)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have i2 : Integrable ((Ioc u₀ 1).indicator (fun u : ℝ => 4 * N / u)) volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hc : ContinuousOn (fun u : ℝ => 4 * N / u) (Icc u₀ 1) :=
      continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hu₀ hu.1).ne'
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have i3 : Integrable ((Ioi 1).indicator (fun u : ℝ => 4 * N * exp (-(1 / 4) * u))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr ((exp_neg_integrableOn_Ioi 1 (by norm_num)).const_mul _)
  have hgi : IntegrableOn g (Ioi 0) := ((i1.add i2).add i3).integrableOn
  have v1 : ∫ u in Ioi 0, (Ioc 0 u₀).indicator (fun _ : ℝ => H * L) u = H * L * u₀ := by
    rw [setIntegral_indicator measurableSet_Ioc, show Ioi (0 : ℝ) ∩ Ioc 0 u₀ = Ioc 0 u₀ by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.1, h⟩, setIntegral_const, Real.volume_real_Ioc_of_le hu₀.le, smul_eq_mul]
    ring
  have v2 : ∫ u in Ioi 0, (Ioc u₀ 1).indicator (fun u : ℝ => 4 * N / u) u = 4 * N * Real.log (1 / u₀) := by
    rw [setIntegral_indicator measurableSet_Ioc, show Ioi (0 : ℝ) ∩ Ioc u₀ 1 = Ioc u₀ 1 by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨lt_trans hu₀ h.1, h⟩, ← intervalIntegral.integral_of_le hu₀1]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hu₀ one_pos, one_mul, one_div]
  have v3 : ∫ u in Ioi 0, (Ioi 1).indicator (fun u : ℝ => 4 * N * exp (-(1 / 4) * u)) u ≤ 16 * N := by
    rw [setIntegral_indicator measurableSet_Ioi, show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 by
      ext x; simp only [mem_inter_iff, mem_Ioi]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩, integral_const_mul, integral_exp_mul_Ioi (by norm_num) 1]
    have : exp (-(1 / 4) * 1) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    have h4 : -exp (-(1 / 4) * 1) / -(1 / 4 : ℝ) = 4 * exp (-(1 / 4) * 1) := by field_simp
    rw [h4]; nlinarith
  calc Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f = ∫ u in Ioi 0, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := rfl
    _ ≤ ∫ u in Ioi 0, g u := setIntegral_mono_on hlevy hgi measurableSet_Ioi hpt
    _ = (∫ u in Ioi 0, (Ioc 0 u₀).indicator (fun _ : ℝ => H * L) u)
        + (∫ u in Ioi 0, (Ioc u₀ 1).indicator (fun u : ℝ => 4 * N / u) u)
        + ∫ u in Ioi 0, (Ioi 1).indicator (fun u : ℝ => 4 * N * exp (-(1 / 4) * u)) u := by
        have e := integral_add (μ := volume.restrict (Ioi 0)) (i1.add i2).integrableOn i3.integrableOn
        have e2 := integral_add (μ := volume.restrict (Ioi 0)) i1.integrableOn i2.integrableOn
        simp only [Pi.add_apply] at e e2
        rw [e, e2]
    _ ≤ H * L * u₀ + 4 * N * Real.log (1 / u₀) + 16 * N := by rw [v1, v2]; linarith

end Cvs.WeilForm.Archimedean.LevyEnergyTwoBounds
