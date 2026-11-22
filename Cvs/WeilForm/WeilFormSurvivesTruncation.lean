import Mathlib
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Finite.WindowedPartialSumsConverge
import Cvs.WeilForm.ArchChannelSurvivesTruncation
import Cvs.WeilForm.Mollify.ChannelsLipschitz
import Cvs.WeilForm.SelfConvolutionFunctional

/-!
# The Weil form survives truncation

    weilForm P R (F_N) → weilForm P R g

`Cvs.WeilForm.Mollify.ChannelsLipschitz` carries the three Lipschitz channels and `Cvs.WeilForm.ArchChannelSurvivesTruncation` the archimedean one.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormSurvivesTruncation

variable {L : ℝ}

/-- A continuous function supported in the window is square integrable. -/
theorem memLp_of_support (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) :
    MemLp g 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable g (volume : Measure ℝ) := hgc.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  have heq : (fun x : ℝ => g x ^ 2)
      = Set.indicator (Set.Ioc (0:ℝ) L) (fun x => g x ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hgs x hx]; norm_num
  rw [heq]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr (hgc.pow 2).integrableOn_Ioc

/-- **The Weil form survives truncation.** -/
theorem tendsto_weilForm_modeSum (hL : 0 < L) (P R : ℕ) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x) :
    Filter.Tendsto (fun N : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
        (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g)))
      Filter.atTop (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  have hgmem : MemLp g 2 (volume : Measure ℝ) := memLp_of_support hL hgc hgs
  have hEnn : 0 ≤ ∫ x : ℝ, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
  refine Cvs.WeilForm.Mollify.ChannelsLipschitz.tendsto_weilForm_of_tendsto_archFull
    (L := L) (C := ∫ x : ℝ, g x ^ 2) P R hEnn hgmem
    (fun N => Cvs.Finite.WindowedModeSumDomain.memLp_windowMode L (Finset.range N) _) hgs
    (fun N => Cvs.Finite.WindowedModeSumDomain.support_windowMode L (Finset.range N) _)
    (fun N => Cvs.Finite.WindowedPartialSumsConverge.integral_windowMode_sq_le hL hgc hgs N)
    (Cvs.Finite.WindowedPartialSumsConverge.tendsto_integral_sub hL hgc hgs hsymm)
    (Cvs.WeilForm.ArchChannelSurvivesTruncation.tendsto_archFull_modeSum hL hgd hg'c hgs hsymm hgmem)

end Cvs.WeilForm.WeilFormSurvivesTruncation
