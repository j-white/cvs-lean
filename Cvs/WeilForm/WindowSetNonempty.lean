import Mathlib
import Cvs.Finite.ConstantModeWindowDamped
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.TruncatedWindowNonzeroTest
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's constraint set is not empty

    `L^{−1/2}·1_{(0,L]} ∈ windowSet L`   for every `L > 0`

the constant mode's Lévy integral converging because its deficit is linear at the origin,
exactly cancelling the density's pole.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowSetNonempty

/-- The window's constant mode. -/
def flat (L : ℝ) : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ))

/-- **The density's pole is simple.**  `densityU u · u` stays bounded near the origin. -/
theorem densityU_mul_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u ≤ 3 := by
  have hden : 0 < 1 - Real.exp (-u) := by
    have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  -- `1 − e^{−u} ≥ u e^{−u}`, from `e^u ≥ 1 + u`
  have hkey : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    have h2 : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-u), h1, h2]
  have hupos : 0 < u * Real.exp (-u) := by positivity
  have hbound : Cvs.WeilForm.Archimedean.LevyDensity.densityU u ≤ Real.exp (-(u / 4)) / (u * Real.exp (-u)) := by
    rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hupos hkey
  have hexp : Real.exp (-(u / 4)) / (u * Real.exp (-u)) * u = Real.exp (3 * u / 4) := by
    have h2 : Real.exp (-(u / 4)) / Real.exp (-u) = Real.exp (3 * u / 4) := by
      rw [← Real.exp_sub]; congr 1; ring
    have hu0 : u ≠ 0 := ne_of_gt hu
    have he : Real.exp (-u) ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (3 * u / 4) ≤ 3 := by
    have h4 : Real.exp (3 * u / 4) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith)
    have h5 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u
      ≤ Real.exp (-(u / 4)) / (u * Real.exp (-u)) * u :=
        mul_le_mul_of_nonneg_right hbound hu.le
    _ = Real.exp (3 * u / 4) := hexp
    _ ≤ 3 := h3

/-- The constant mode is square integrable. -/
theorem memLp_flat (L : ℝ) : MemLp (flat L) 2 (volume : Measure ℝ) := by
  rw [flat]
  refine memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet (1:ℝ) (Or.inr ?_)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- **The constant mode's energy is the window's length.** -/
theorem integral_flat_sq {L : ℝ} (hL : 0 ≤ L) : (∫ x : ℝ, flat L x ^ 2) = L := by
  have hsq : (fun x : ℝ => flat L x ^ 2) = flat L := by
    funext x
    rw [flat]
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  rw [hsq, flat, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le hL]
  simp

/-- **The constant mode's deficit is at most the displacement.** -/
theorem deficit_flat_le {L : ℝ} (hL : 0 ≤ L) {u : ℝ} (hu : 0 < u) :
    selfConvolution (flat L) 0 - selfConvolution (flat L) (u / 2) ≤ u / 2 := by
  rw [flat, Cvs.WeilForm.TruncatedWindowNonzeroTest.selfConvolution_one_zero hL]
  by_cases hcase : u / 2 ≤ L
  · rw [Cvs.Finite.ConstantModeWindowDamped.selfConvolution_indicator_one (by linarith) hcase]
    linarith
  · push Not at hcase
    rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L (fun _ => (1:ℝ))
      (by rw [abs_of_pos (by linarith : (0:ℝ) < u / 2)]; linarith)]
    linarith

/-- **The constant mode's deficit is at most the window's length.** -/
theorem deficit_flat_le_len {L : ℝ} (hL : 0 ≤ L) {u : ℝ} (hu : 0 < u) :
    selfConvolution (flat L) 0 - selfConvolution (flat L) (u / 2) ≤ L := by
  rw [flat, Cvs.WeilForm.TruncatedWindowNonzeroTest.selfConvolution_one_zero hL]
  by_cases hcase : u / 2 ≤ L
  · rw [Cvs.Finite.ConstantModeWindowDamped.selfConvolution_indicator_one (by linarith) hcase]
    linarith
  · rw [not_le] at hcase
    rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L (fun _ => (1:ℝ))
      (by rw [abs_of_pos (by linarith : (0:ℝ) < u / 2)]; linarith)]
    linarith

theorem support_flat (L : ℝ) : ∀ s ∉ Set.Ioc (0:ℝ) L, flat L s = 0 := by
  intro s hs
  rw [flat, Set.indicator_of_notMem hs]

/-- **The constant mode's Lévy integral converges.** -/
theorem integrableOn_levy_flat {L : ℝ} (hL : 0 < L) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (flat L)) (Set.Ioi 0) (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (flat L))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (memLp_flat L)).aestronglyMeasurable
  have hnn : ∀ u : ℝ, 0 < u → 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (flat L) u := by
    intro u hu
    rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
    refine mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu).le ?_
    have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2) (memLp_flat L)
    linarith
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- the pole is simple, so the deficit tames it
    have hg : IntegrableOn (fun _ : ℝ => (3:ℝ) / 2) (Set.Ioc (0:ℝ) 1) (volume : Measure ℝ) := by
      refine integrableOn_const (C := (3:ℝ) / 2) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    refine Integrable.mono' hg (hmeas.mono_set Set.Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu.1
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
    have hdef := deficit_flat_le hL.le hu0
    have hd := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    have hmul := densityU_mul_le hu0 hu.2
    nlinarith [hd, hdef, hmul, hu0]
  · -- far out the density is integrable and the deficit is bounded
    have hsub : Set.Ioi (1:ℝ) ⊆ Set.Ioi (0:ℝ) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
    have hg : IntegrableOn (fun u : ℝ => L * Cvs.WeilForm.Archimedean.LevyDensity.densityU u) (Set.Ioi 1)
        (volume : Measure ℝ) :=
      (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU (by norm_num : (0:ℝ) < 1)).const_mul L
    refine Integrable.mono' hg (hmeas.mono_set hsub) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := by simp only [Set.mem_Ioi] at hu; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
    have hdef := deficit_flat_le_len hL.le hu0
    have hd := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    nlinarith [hd, hdef]

/-- **The window's constraint set has a member.** -/
theorem flat_normalised_mem {L : ℝ} (hL : 0 < L) :
    (fun x => (Real.sqrt L)⁻¹ * flat L x) ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
  have h := Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised (memLp_flat L) (support_flat L)
    (integrableOn_levy_flat hL) (by rw [integral_flat_sq hL.le]; exact hL)
  rw [integral_flat_sq hL.le] at h
  exact h

end Cvs.WeilForm.WindowSetNonempty
