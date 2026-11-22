import Mathlib
import Cvs.Upstream.EntireFamilyEquicontinuous
import Cvs.Upstream.EquicontinuousRangeCoe

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A bound on a larger ball makes the restrictions relatively compact

`arzela_ascoli` takes a compact target set and one equicontinuity hypothesis, and the bound on the
ball of radius `r + δ` supplies both: the values on the ball of radius `r` lie in the closed ball of
radius `M`, and `Cvs.Upstream.EntireFamilyEquicontinuous.equicontinuous_restrict` is already stated on that subtype.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Metric BoundedContinuousFunction

namespace Cvs.Upstream.EntireFamilyRelativelyCompact

variable {ι : Type*}

/-- The family restricted to a closed ball, as bounded continuous functions. -/
def restrictBCF (r : ℝ) {F : ι → ℂ → ℂ} (hcont : ∀ i, Continuous (F i)) (i : ι) :
    ↥(closedBall (0 : ℂ) r) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.restrict (closedBall (0 : ℂ) r) ⟨F i, hcont i⟩)

/-- **Relative compactness on a closed ball**, for a family of entire functions bounded on a
slightly larger one. -/
theorem isCompact_closure_range {F : ι → ℂ → ℂ} {r δ M : ℝ}
    (hd : ∀ i, Differentiable ℂ (F i)) (hδ : 0 < δ)
    (hbd : ∀ (i : ι) (z : ℂ), ‖z‖ ≤ r + δ → ‖F i z‖ ≤ M) :
    IsCompact (closure (Set.range (restrictBCF r (fun i => (hd i).continuous)))) := by
  refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M)
    (isCompact_closedBall 0 M) _ ?_ ?_
  · intro g x hg
    obtain ⟨i, rfl⟩ := hg
    rw [mem_closedBall, dist_zero_right]
    exact hbd i _ (le_trans (mem_closedBall_zero_iff.mp x.2) (by linarith))
  · refine Cvs.Upstream.EquicontinuousRangeCoe.equicontinuous_range_coe
      (fun g : ↥(closedBall (0 : ℂ) r) →ᵇ ℂ => (g : ↥(closedBall (0 : ℂ) r) → ℂ)) ?_
    exact Cvs.Upstream.EntireFamilyEquicontinuous.equicontinuous_restrict hd hδ hbd

end Cvs.Upstream.EntireFamilyRelativelyCompact
