import Mathlib
import Cvs.Upstream.EquicontinuousRangeCoe
import Cvs.Upstream.EquicontinuousRestrictCompact

/-!
# A bounded equicontinuous family is relatively compact on a compact interval

    ‖F i x‖ ≤ M and `Equicontinuous F`  ⟹  the restrictions to `[−T, T]` have compact closure

`arzela_ascoli`, with the range in a closed ball and the equicontinuity supplied by `Cvs.Upstream.EquicontinuousRestrictCompact`
and `Cvs.Upstream.EquicontinuousRangeCoe`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Metric BoundedContinuousFunction

namespace Cvs.Upstream.BoundedEquicontinuousCompactClosure

variable {ι : Type*}

/-- The family restricted to a compact interval, as bounded continuous functions. -/
def restrictBCF (T : ℝ) {F : ι → ℝ → ℂ} (hcont : ∀ i, Continuous (F i)) (i : ι) :
    ↥(Icc (-T) T) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.restrict (Icc (-T) T) ⟨F i, hcont i⟩)

/-- **Relative compactness on a compact interval.** -/
theorem isCompact_closure_range (T : ℝ) {F : ι → ℝ → ℂ} (hcont : ∀ i, Continuous (F i))
    {M : ℝ} (hbd : ∀ (i : ι) (x : ℝ), ‖F i x‖ ≤ M) (heq : Equicontinuous F) :
    IsCompact (closure (Set.range (restrictBCF T hcont))) := by
  refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M)
    (isCompact_closedBall 0 M) _ ?_ ?_
  · intro g x hg
    obtain ⟨i, rfl⟩ := hg
    rw [mem_closedBall, dist_zero_right]
    exact hbd i _
  · refine Cvs.Upstream.EquicontinuousRangeCoe.equicontinuous_range_coe
      (fun g : ↥(Icc (-T) T) →ᵇ ℂ => (g : ↥(Icc (-T) T) → ℂ)) ?_
    exact Cvs.Upstream.EquicontinuousRestrictCompact.equicontinuous_restrict heq (Icc (-T) T)

end Cvs.Upstream.BoundedEquicontinuousCompactClosure
