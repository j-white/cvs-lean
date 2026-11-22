import Mathlib
import Cvs.Finite.CoefficientMassFinite
import Cvs.Finite.ModeSumDerivativeEnergy
import Cvs.Finite.PartialSumDerivEnergyBound
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Finite.WindowedPartialSumsConverge
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.Zeta.WeilPositivityStatement

/-!
# The archimedean channel survives truncation

    archFull (F_N) → archFull g

by dominated convergence: `Cvs.Finite.WindowedPartialSumsConverge` gives the pointwise limit, and `Cvs.Finite.WindowedModeSumDomain`'s bound with
`Cvs.Finite.ModeSumDerivativeEnergy`, `Cvs.Finite.PartialSumDerivEnergyBound`, `Cvs.Finite.CoefficientMassFinite`'s ceilings gives a majorant that does not move with `N`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ArchChannelSurvivesTruncation

variable {L : ℝ}

/-- The constant mode carries no derivative energy, so the two weightings agree. -/
theorem derivEnergy_eq (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ s, (if n = 0 then 2 else 1) * (2 * π * n / L) ^ 2 * a n ^ 2)
      = ∑ n ∈ s, (2 * π * n / L) ^ 2 * a n ^ 2 := by
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; norm_num
  · rw [if_neg hn]; ring

/-- **The archimedean channel survives truncation.** -/
theorem tendsto_archFull_modeSum (hL : 0 < L) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x)
    (hgmem : MemLp g 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun N : ℕ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
        (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g)))
      Filter.atTop (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g)) := by
  classical
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  -- the three ceilings
  set Dinf : ℝ := ∫ x in (0:ℝ)..L, g' x ^ 2 with hDinf
  have hDinfnn : 0 ≤ Dinf := by
    rw [hDinf]; exact intervalIntegral.integral_nonneg hL.le fun x _ => sq_nonneg _
  set Binf : ℝ := ∑' n : ℕ, |a n| with hBinf
  have hsummable : Summable (fun n : ℕ => |a n|) := by
    rw [ha]; exact Cvs.Finite.CoefficientMassFinite.summable_abs hL hgd hg'c
  have hBinfnn : 0 ≤ Binf := by
    rw [hBinf]; exact tsum_nonneg fun n => abs_nonneg _
  set Einf : ℝ := ∫ x : ℝ, g x ^ 2 with hEinf
  have hEinfnn : 0 ≤ Einf := by
    rw [hEinf]; exact integral_nonneg fun x => sq_nonneg _
  set c₀ : ℝ := min 1 (2 * L) with hc₀
  have hc₀pos : 0 < c₀ := lt_min one_pos (by linarith)
  set K : ℝ := 3 * (c₀ / 8 * Dinf + Binf ^ 2 / 2) with hK
  -- the majorant
  set maj : ℝ → ℝ := fun u =>
    Set.indicator (Set.Ioc (0:ℝ) c₀) (fun _ => K) u
      + Set.indicator (Set.Ioi c₀) (fun u => 2 * Einf * Cvs.WeilForm.Archimedean.LevyDensity.densityU u) u
    with hmaj
  have hp1 : Integrable (Set.indicator (Set.Ioc (0:ℝ) c₀) (fun _ => K))
      (volume : Measure ℝ) := by
    refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
    refine integrableOn_const (C := K) ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hp2 : Integrable (Set.indicator (Set.Ioi c₀)
      (fun u => 2 * Einf * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)) (volume : Measure ℝ) := by
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
    exact (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU hc₀pos).const_mul (2 * Einf)
  have hmajint : IntegrableOn maj (Set.Ioi 0) (volume : Measure ℝ) :=
    (hp1.add hp2).integrableOn
  -- the three ceilings, per truncation
  have hDle : ∀ N : ℕ, L / 2 * ∑ n ∈ Finset.range N,
      (if n = 0 then 2 else 1) * (2 * π * n / L) ^ 2 * a n ^ 2 ≤ Dinf := by
    intro N
    rw [derivEnergy_eq, ← Cvs.Finite.ModeSumDerivativeEnergy.integral_modeSumDeriv_sq hL, hDinf, ha]
    exact Cvs.Finite.PartialSumDerivEnergyBound.integral_modeSumDeriv_sq_le hL hgd hg'c (Finset.range N)
  have hDnn : ∀ N : ℕ, 0 ≤ L / 2 * ∑ n ∈ Finset.range N,
      (if n = 0 then 2 else 1) * (2 * π * n / L) ^ 2 * a n ^ 2 := by
    intro N
    refine mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => ?_)
    have hw : (0:ℝ) ≤ (if n = 0 then 2 else 1) := by by_cases h : n = 0 <;> simp [h]
    positivity
  have hBle : ∀ N : ℕ, ∑ n ∈ Finset.range N, |a n| ≤ Binf := by
    intro N
    rw [hBinf]
    exact hsummable.sum_le_tsum (Finset.range N) (fun n _ => abs_nonneg _)
  have hBnn : ∀ N : ℕ, 0 ≤ ∑ n ∈ Finset.range N, |a n| :=
    fun N => Finset.sum_nonneg fun n _ => abs_nonneg _
  have hEle : ∀ N : ℕ, (∫ x : ℝ, Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a x ^ 2)
      ≤ Einf := by
    intro N
    rw [hEinf, ha]
    exact Cvs.Finite.WindowedPartialSumsConverge.integral_windowMode_sq_le hL hgc hgs N
  -- dominated convergence
  refine tendsto_integral_filter_of_dominated_convergence maj ?_ ?_ hmajint ?_
  · refine Filter.Eventually.of_forall fun N => ?_
    exact Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
        (Cvs.Finite.WindowedModeSumDomain.memLp_windowMode L (Finset.range N) a)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun N => ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a) 0
          - selfConvolution (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a) (u / 2)) := by
      refine mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le ?_
      have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2)
        (Cvs.Finite.WindowedModeSumDomain.memLp_windowMode L (Finset.range N) a)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hmaj]
    simp only
    by_cases hc : u ≤ c₀
    · have hmem : u ∈ Set.Ioc (0:ℝ) c₀ := ⟨hu0, hc⟩
      have hnot : u ∉ Set.Ioi c₀ := by simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]
      have hu1 : u ≤ 1 := le_trans hc (by rw [hc₀]; exact min_le_left _ _)
      have huL : u ≤ 2 * L := le_trans hc (by rw [hc₀]; exact min_le_right _ _)
      have hnear := Cvs.Finite.WindowedModeSumDomain.levy_le_near hL (Finset.range N) a hu0 hu1 huL
      simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy] at hnear
      have h1 := hDle N
      have h2 := hBle N
      have h3 := hDnn N
      have h4 := hBnn N
      rw [hK]
      nlinarith [hnear, h1, h2, h3, h4, hDinfnn, hBinfnn, hc, hu0]
    · push_neg at hc
      have hmem : u ∈ Set.Ioi c₀ := hc
      have hnot : u ∉ Set.Ioc (0:ℝ) c₀ := by
        simp only [Set.mem_Ioc, not_and_or, not_le]
        exact Or.inr hc
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, zero_add]
      have hdef := Cvs.Finite.WindowedModeSumDomain.deficit_le_two_energy L (Finset.range N) a (u / 2)
      have hd := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
      nlinarith [hdef, hd, hEle N]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u _ => ?_)
    have h := Cvs.Finite.WindowedPartialSumsConverge.tendsto_levy hL hgc hgs hsymm hgmem u
    simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy] at h
    rw [ha]
    exact h

end Cvs.WeilForm.ArchChannelSurvivesTruncation
