import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The channel quadratic form as a windowed double integral

    `∫ s, f s · ∫ u, f u · e^{−b|s−u|} = ∫₀^L f s · (∫₀^L f u · e^{−b|s−u|}) ds`

for continuous `f` supported in `[0, L]`.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.ChannelQuadWindowed

/-- **The inner kernel integral restricts to the window.** -/
theorem inner_restrict {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) (b s : ℝ) :
    (∫ u, f u * Real.exp (-(b * |s - u|))) = ∫ u in (0:ℝ)..L, f u * Real.exp (-(b * |s - u|)) := by
  rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) L)
      (fun x hx => by rw [hsupp x hx, zero_mul])]

/-- **The channel quadratic form as a windowed double integral.** -/
theorem channelQuad_window {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) (b : ℝ) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ s in (0:ℝ)..L, f s * ∫ u in (0:ℝ)..L, f u * Real.exp (-(b * |s - u|)) := by
  rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) L)
      (fun x hx => by rw [hsupp x hx, zero_mul])]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [inner_restrict hL hsupp b s]

end Cvs.WeilForm.ChannelQuadWindowed
