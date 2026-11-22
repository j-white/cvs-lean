import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# The per-channel Lévy integrand equals `(2/b) g(0)` minus the channel quadratic form

    `∫_{u>0} e^{−b u/2} (g(0) − g(u/2)) du = (2/b) g(0) − ∫ s, f s · ∫ u, f u · e^{−b|s−u|}`

for continuous, compactly supported `f`, with `g = selfConvolution f`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped Pointwise

namespace Cvs.WeilForm.ChannelLevyIntegrand

/-- **The self-convolution of a compactly supported function has compact support.** -/
theorem hasCompactSupport_selfConvolution {f : ℝ → ℝ} (hcf : HasCompactSupport f) :
    HasCompactSupport (selfConvolution f) := by
  apply HasCompactSupport.intro (K := tsupport f + -tsupport f)
    (hcf.isCompact.add hcf.isCompact.neg)
  intro v hv
  unfold selfConvolution
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases h1 : f s = 0
  · simp [h1]
  · by_cases h2 : f (s + v) = 0
    · simp [h2]
    · exact absurd (Set.mem_add.mpr ⟨s + v, subset_tsupport f h2, -s,
        Set.mem_neg.mpr (by simpa using subset_tsupport f h1), by ring⟩) hv

end Cvs.WeilForm.ChannelLevyIntegrand
