import Mathlib
import Cvs.Finite.ModeSumDeficit
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WindowSetNonempty
import Cvs.Zeta.WeilPositivityStatement

/-!
# The windowed mode sum lies in the domain, with a majorant read off its coefficients

    levy F u ≤ 3·(u/8·D + B²/2)  near the origin,   levy F u ≤ 2E·densityU u  away from it

`D`, `B` and `E` being the derivative energy, the coefficient mass and the energy.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.WindowedModeSumDomain

variable {L : ℝ} {s : Finset ℕ} {a : ℕ → ℝ}

/-- The windowed mode sum. -/
def windowMode (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)

theorem continuous_modeSum (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a) := by
  show Continuous fun x : ℝ => ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)
  exact continuous_finsetSum _ (fun n _ => by fun_prop)

theorem memLp_windowMode (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    MemLp (windowMode L s a) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (windowMode L s a) (volume : Measure ℝ) := by
    rw [windowMode]
    exact (continuous_modeSum L s a).aestronglyMeasurable.indicator measurableSet_Ioc
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  have heq : (fun x : ℝ => windowMode L s a x ^ 2)
      = Set.indicator (Set.Ioc (0:ℝ) L) (fun x => Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x ^ 2) := by
    funext x
    rw [windowMode]
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; norm_num
  rw [heq]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    ((continuous_modeSum L s a).pow 2).integrableOn_Ioc

theorem support_windowMode (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    ∀ x ∉ Set.Ioc (0:ℝ) L, windowMode L s a x = 0 := by
  intro x hx
  rw [windowMode, Set.indicator_of_notMem hx]

/-- **The deficit is at most twice the energy, always.** -/
theorem deficit_le_two_energy (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (v : ℝ) :
    selfConvolution (windowMode L s a) 0 - selfConvolution (windowMode L s a) v
      ≤ 2 * ∫ x : ℝ, windowMode L s a x ^ 2 := by
  have h0 := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le (0:ℝ) (memLp_windowMode L s a)
  have hv := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le v (memLp_windowMode L s a)
  linarith [(abs_le.mp h0).2, (abs_le.mp hv).1]

/-- **Near the origin the deficit's linear and quadratic terms both survive the pole.** -/
theorem levy_le_near (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (hu1 : u ≤ 1) (huL : u ≤ 2 * L) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (windowMode L s a) u
      ≤ 3 * (u / 8 * (L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
              * (2 * π * n / L) ^ 2 * a n ^ 2)
        + (∑ n ∈ s, |a n|) ^ 2 / 2) := by
  have hdef := Cvs.Finite.ModeSumDeficit.deficit_le hL (by linarith : (0:ℝ) ≤ u / 2)
    (by linarith : u / 2 ≤ L) s a
  have hmul := Cvs.WeilForm.WindowSetNonempty.densityU_mul_le hu hu1
  have hd := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu
  have hDnn : 0 ≤ L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
      * (2 * π * (n : ℝ) / L) ^ 2 * a n ^ 2 := by
    refine mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => ?_)
    have hw : (0:ℝ) ≤ (if n = 0 then 2 else 1) := by by_cases h : n = 0 <;> simp [h]
    positivity
  have hBnn : (0:ℝ) ≤ (∑ n ∈ s, |a n|) ^ 2 := sq_nonneg _
  rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, windowMode] at *
  set D : ℝ := L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
    * (2 * π * (n : ℝ) / L) ^ 2 * a n ^ 2 with hD
  set B2 : ℝ := (∑ n ∈ s, |a n|) ^ 2 with hB2
  set def2 : ℝ := selfConvolution ((Set.Ioc (0:ℝ) L).indicator
    (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) 0
    - selfConvolution ((Set.Ioc (0:ℝ) L).indicator
      (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) (u / 2) with hdef2
  have hdef' : def2 ≤ u ^ 2 / 8 * D + u / 2 * B2 := by nlinarith [hdef]
  have h1 : Cvs.WeilForm.Archimedean.LevyDensity.densityU u * def2
      ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (u ^ 2 / 8 * D + u / 2 * B2) :=
    mul_le_mul_of_nonneg_left hdef' hd.le
  have hnn : 0 ≤ u / 8 * D + B2 / 2 := by nlinarith [hDnn, hBnn, hu]
  have h3 : (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u) * (u / 8 * D + B2 / 2)
      ≤ 3 * (u / 8 * D + B2 / 2) := mul_le_mul_of_nonneg_right hmul hnn
  nlinarith [h1, h3]

/-- **The windowed mode sum lies in the domain.** -/
theorem integrableOn_levy_windowMode (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (windowMode L s a)) (Set.Ioi 0)
      (volume : Measure ℝ) := by
  set c₀ : ℝ := min 1 (2 * L) with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact lt_min one_pos (by linarith)
  set D : ℝ := L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
    * (2 * π * (n : ℝ) / L) ^ 2 * a n ^ 2 with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    refine mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => ?_)
    have hw : (0:ℝ) ≤ (if n = 0 then 2 else 1) := by by_cases h : n = 0 <;> simp [h]
    positivity
  set B2 : ℝ := (∑ n ∈ s, |a n|) ^ 2 with hB2
  set E : ℝ := ∫ x : ℝ, windowMode L s a x ^ 2 with hE
  have hmeas : AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (windowMode L s a))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
        (memLp_windowMode L s a)).aestronglyMeasurable
  have hnn : ∀ u : ℝ, 0 < u → 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (windowMode L s a) u := by
    intro u hu
    rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
    refine mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu).le ?_
    have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2)
      (memLp_windowMode L s a)
    linarith
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 c₀ ∪ Set.Ioi c₀ :=
    (Set.Ioc_union_Ioi_eq_Ioi hc₀pos.le).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun _ : ℝ => 3 * (c₀ / 8 * D + B2 / 2)) (Set.Ioc (0:ℝ) c₀)
        (volume : Measure ℝ) := by
      refine integrableOn_const (C := 3 * (c₀ / 8 * D + B2 / 2)) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    refine Integrable.mono' hg (hmeas.mono_set Set.Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu.1
    have huc : u ≤ c₀ := hu.2
    have hu1 : u ≤ 1 := le_trans huc (by rw [hc₀]; exact min_le_left _ _)
    have huL : u ≤ 2 * L := le_trans huc (by rw [hc₀]; exact min_le_right _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0)]
    have hnear := levy_le_near hL s a hu0 hu1 huL
    rw [← hD, ← hB2] at hnear
    nlinarith [hnear, hDnn, huc]
  · have hsub : Set.Ioi c₀ ⊆ Set.Ioi (0:ℝ) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
    have hg : IntegrableOn (fun u : ℝ => 2 * E * Cvs.WeilForm.Archimedean.LevyDensity.densityU u) (Set.Ioi c₀)
        (volume : Measure ℝ) :=
      (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU hc₀pos).const_mul (2 * E)
    refine Integrable.mono' hg (hmeas.mono_set hsub) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := by simp only [Set.mem_Ioi] at hu; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
    have hdef := deficit_le_two_energy L s a (u / 2)
    rw [← hE] at hdef
    nlinarith [hdef, (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0)]

end Cvs.Finite.WindowedModeSumDomain
