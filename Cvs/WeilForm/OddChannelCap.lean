import Mathlib
import Cvs.WeilForm.ChannelCapEnergyPoincare
import Cvs.WeilForm.ChannelGreenOddPoincare

/-!
# The per-channel odd cap (G1 for continuous compactly supported odd sources)

    `∫ s, f s · ∫ u, f u · e^{−b|s−u|} ≤ (2b/(b²+t²)) · ∫ f²`

for continuous `f` supported in `[0, L]` with `f(L−s) = −f(s)`, at a pole-free frequency `t`.
-/

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.OddChannelCap

/-- **The per-channel odd cap.** -/
theorem odd_channel_cap {f : ℝ → ℝ} {L b t : ℝ} (hf : Continuous f)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) (hodd : ∀ s, f (L - s) = -f s)
    (hL : 0 < L) (hb : 0 < b) (ht : 0 < t)
    (hfree : t * (L / 2) < π / 2 + Real.arctan (b / t)) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      ≤ (2 * b / (b ^ 2 + t ^ 2)) * ∫ x, f x ^ 2 :=
  Cvs.WeilForm.ChannelCapEnergyPoincare.channel_cap hL.le hf hsupp hb ht
    (Cvs.WeilForm.ChannelGreenOddPoincare.poincare_odd hf hodd hL hb ht hfree)

end Cvs.WeilForm.OddChannelCap
