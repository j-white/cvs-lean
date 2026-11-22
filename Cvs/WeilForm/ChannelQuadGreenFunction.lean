import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.ChannelQuadWindowed

/-!
# The channel quadratic form is the pairing of `f` with its Green's function

    `∫ s, f s · ∫ u, f u · e^{−b|s−u|} = ∫₀^L f s · convSplit b L f s ds`

for continuous `f` supported in `[0, L]`, with `convSplit` (Cvs.Finite.ExponentialKernelLocalises) the channel Green's function.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.ChannelQuadGreenFunction

/-- **The channel quadratic form as the pairing with the Green's function.** -/
theorem channelQuad_convSplit {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : Continuous f)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) (b : ℝ) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ s in (0:ℝ)..L, f s * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s := by
  rw [Cvs.WeilForm.ChannelQuadWindowed.channelQuad_window hL hsupp b]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc (0:ℝ) L := by rwa [uIcc_of_le hL] at hs
  have hcs := Cvs.Finite.ExponentialKernelLocalises.convSplit_eq (b := b) (L := L) (f := f) hs'.1 hs'.2 hf
  rw [hcs]
  refine congrArg (f s * ·) ?_
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm]
  congr 2
  ring

end Cvs.WeilForm.ChannelQuadGreenFunction
