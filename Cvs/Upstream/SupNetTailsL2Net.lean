import Mathlib
import Cvs.Upstream.SupBoundIntervalL2
import Cvs.Upstream.TightnessLocalToGlobalL2

/-!
# A sup-net member with small tails is an `L²`-net member

    sup within δ on `[−T,T]`, tails ≤ ε on both, δ²·2T ≤ ε  ⟹  ∫_ℝ ‖f − g‖² ≤ 5ε

`Cvs.Upstream.SupBoundIntervalL2` for the middle and `Cvs.Upstream.TightnessLocalToGlobalL2` for the tails, in the form the net argument consumes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.Upstream.SupNetTailsL2Net

/-- **The transfer.**  A member of a sup-norm net on the interval, whose tail is controlled,
is a member of an `L²` net on the line. -/
theorem integral_sq_le_of_sup_and_tails {f g : ℝ → ℂ} {T δ ε : ℝ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hdiff : Integrable fun t => ‖f t - g t‖ ^ 2)
    (hf : Integrable fun t => ‖f t‖ ^ 2)
    (hg : Integrable fun t => ‖g t‖ ^ 2)
    (hsup : ∀ t ∈ Icc (-T) T, ‖f t - g t‖ ≤ δ)
    (hδε : δ ^ 2 * (2 * T) ≤ ε)
    (htf : (∫ t in (Icc (-T) T)ᶜ, ‖f t‖ ^ 2) ≤ ε)
    (htg : (∫ t in (Icc (-T) T)ᶜ, ‖g t‖ ^ 2) ≤ ε) :
    (∫ t : ℝ, ‖f t - g t‖ ^ 2) ≤ 5 * ε := by
  have hmid := Cvs.Upstream.SupBoundIntervalL2.setIntegral_sq_le_of_sup hT hδ hdiff.integrableOn hsup
  exact Cvs.Upstream.TightnessLocalToGlobalL2.integral_sq_le_of_tails hT hdiff hf hg
    (le_trans hmid hδε) htf htg

end Cvs.Upstream.SupNetTailsL2Net
