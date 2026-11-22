import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.PoleChannelWindowL2
import Cvs.WeilForm.PrimeChannelL2Continuous
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# Every channel but the archimedean one is Lipschitz in the `L²` distance

    |(W F − arch F) − (W g − arch g)|  ≤  √(∫ (F−g)²) · formMod L C P R g

so the archimedean channel is the only place a one-sided hypothesis is ever needed.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Mollify.ChannelsLipschitz

/-- The Lipschitz constant of the three easy channels. -/
def formMod (L C : ℝ) (P R : ℕ) (g : ℝ → ℝ) : ℝ :=
  2 * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
      * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2)
      * (Real.sqrt C + Real.sqrt (∫ x : ℝ, g x ^ 2))
    + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| * (Real.sqrt C + Real.sqrt (∫ x : ℝ, g x ^ 2))
    + 2 * (Real.sqrt C + Real.sqrt (∫ x : ℝ, g x ^ 2))
        * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R

theorem formMod_nonneg (L C : ℝ) (P R : ℕ) (g : ℝ → ℝ) (hC : 0 ≤ C) :
    0 ≤ formMod L C P R g := by
  have hmass : 0 ≤ Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  rw [formMod]
  positivity

/-- **The three easy channels move by at most the `L²` distance.** -/
theorem abs_weilForm_sub_archFull_sub_le {L C : ℝ} (P R : ℕ) {g F : ℝ → ℝ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hF : MemLp F 2 (volume : Measure ℝ))
    (hgs : ∀ s ∉ Set.Ioc (0:ℝ) L, g s = 0) (hFs : ∀ s ∉ Set.Ioc (0:ℝ) L, F s = 0)
    (hbdd : (∫ x : ℝ, F x ^ 2) ≤ C) :
    |(Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R F - Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull F)
        - (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g - Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g)|
      ≤ Real.sqrt (∫ x : ℝ, (F x - g x) ^ 2) * formMod L C P R g := by
  set s : ℝ := Real.sqrt (∫ x : ℝ, (F x - g x) ^ 2) with hs
  set Eg : ℝ := Real.sqrt (∫ x : ℝ, g x ^ 2) with hEg
  set Bc : ℝ := Real.sqrt C + Eg with hBc
  set Wp : ℝ := Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2) with hWp
  set Wn : ℝ := Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2) with hWn
  set a : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 with ha
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hEgnn : 0 ≤ Eg := Real.sqrt_nonneg _
  have hWpnn : 0 ≤ Wp := Real.sqrt_nonneg _
  have hWnnn : 0 ≤ Wn := Real.sqrt_nonneg _
  have hmassnn : 0 ≤ Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hCnn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hBcnn : 0 ≤ Bc := by rw [hBc]; positivity
  have hEn : Real.sqrt (∫ x : ℝ, F x ^ 2) ≤ Real.sqrt C := Real.sqrt_le_sqrt hbdd
  have hKle : s * (Real.sqrt (∫ x : ℝ, F x ^ 2) + Eg) ≤ s * Bc := by
    refine mul_le_mul_of_nonneg_left ?_ hsnn
    rw [hBc]; linarith
  -- pole channel
  have hpole := Cvs.WeilForm.PoleChannelWindowL2.abs_poleTerm_sub_le hF hg hFs hgs
  have hpole' : |2 * (∫ x : ℝ, F x * Real.exp (x / 2)) * (∫ x : ℝ, F x * Real.exp (-(x / 2)))
      - 2 * (∫ x : ℝ, g x * Real.exp (x / 2)) * (∫ x : ℝ, g x * Real.exp (-(x / 2)))|
      ≤ s * (2 * Wp * Wn * Bc) := by
    refine le_trans hpole ?_
    have : 2 * s * Wp * Wn * (Real.sqrt (∫ x : ℝ, F x ^ 2) + Eg)
        ≤ 2 * s * Wp * Wn * Bc := by
      refine mul_le_mul_of_nonneg_left (by rw [hBc]; linarith) (by positivity)
    nlinarith [this]
  -- the value at the origin
  have hzero := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le (f := F) (h := g) 0 hF hg
  have hzero' : |a * selfConvolution F 0 - a * selfConvolution g 0| ≤ s * (|a| * Bc) := by
    have hrw : a * selfConvolution F 0 - a * selfConvolution g 0
        = a * (selfConvolution F 0 - selfConvolution g 0) := by ring
    rw [hrw, abs_mul]
    have h1 : |selfConvolution F 0 - selfConvolution g 0| ≤ s * Bc := le_trans hzero hKle
    nlinarith [abs_nonneg a, hsnn, hBcnn]
  -- prime channel
  have hprime := Cvs.WeilForm.PrimeChannelL2Continuous.abs_primeSide_sub_le P R hF hg
  have hprime' : |primePowerSideTruncated P R (selfConvolution F)
      - primePowerSideTruncated P R (selfConvolution g)|
      ≤ s * (2 * Bc * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R) := by
    refine le_trans hprime ?_
    nlinarith [hKle, hmassnn, hsnn, hBcnn]
  -- assemble
  have hAg : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution g 0 - selfConvolution g (u / 2)) := rfl
  have hAF : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull F
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution F 0 - selfConvolution F (u / 2)) := rfl
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, hAg, hAF, formMod,
    ← hEg, ← hBc, ← hWp, ← hWn, ← ha]
  have hp := abs_le.mp hpole'
  have hz := abs_le.mp hzero'
  have hpr := abs_le.mp hprime'
  rw [abs_le]
  constructor <;> [linarith [hp.1, hz.1, hpr.2]; linarith [hp.2, hz.2, hpr.1]]

/-- **The form follows the archimedean channel.** -/
theorem tendsto_weilForm_of_tendsto_archFull {L C : ℝ} (P R : ℕ) {g : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hC : 0 ≤ C) (hg : MemLp g 2 (volume : Measure ℝ))
    (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hgs : ∀ s ∉ Set.Ioc (0:ℝ) L, g s = 0)
    (hFs : ∀ n, ∀ s ∉ Set.Ioc (0:ℝ) L, F n s = 0)
    (hbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ C)
    (hconv : Tendsto (fun n : ℕ => ∫ x : ℝ, (F n x - g x) ^ 2) atTop (nhds 0))
    (harch : Tendsto (fun n : ℕ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)) atTop
      (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g))) :
    Tendsto (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n)) atTop
      (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ, (F n x - g x) ^ 2) with hs
  have hstend : Tendsto s atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [hs, Real.sqrt_zero, Function.comp_def] using this
  have hprod : Tendsto (fun n : ℕ => s n * formMod L C P R g) atTop (nhds 0) := by
    have := hstend.mul_const (formMod L C P R g)
    simpa using this
  -- the easy channels converge
  have heasy : Tendsto (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n)
      - Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)) atTop
      (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g - Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hprod ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hb := abs_weilForm_sub_archFull_sub_le (L := L) (C := C) P R hg (hF n) hgs (hFs n)
      (hbdd n)
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (formMod_nonneg L C P R g hC))] at hd
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hb hd
  have := heasy.add harch
  simpa using this

/-- **A channel squeezed from above and semicontinuous from below converges.** -/
theorem tendsto_archFull_of_le {C : ℝ} {g : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hgc : AEStronglyMeasurable (selfConvolution g) (volume : Measure ℝ))
    (hFc : ∀ n, AEStronglyMeasurable (selfConvolution (F n)) (volume : Measure ℝ))
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Set.Ioi 0) (volume : Measure ℝ))
    (hFint : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (F n)) (Set.Ioi 0)
      (volume : Measure ℝ))
    (hconv : Tendsto (fun n : ℕ => ∫ x : ℝ, (F n x - g x) ^ 2) atTop (nhds 0))
    (hbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ C)
    (hle : ∀ n, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n) ≤ b n)
    (hb : Tendsto b atTop (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g))) :
    Tendsto (fun n : ℕ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)) atTop
      (nhds (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlow := Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.archFull_le_eventually (C := C) hg hgc hint hF hFc hFint
    hconv hbdd (by linarith : (0:ℝ) < ε / 2)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hlow
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hb (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, abs_lt] at h2
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith [hle n, h2.2]⟩

end Cvs.WeilForm.Mollify.ChannelsLipschitz
