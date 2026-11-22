import Mathlib
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy channel is a sum of squares

A self-convolution's drop from its value at zero is half the integral of the squared
difference of the function and its translate, so it is never negative; against a positive
density the Lévy channel of any square-integrable function is therefore non-negative, on every
window and with no hypothesis on the zeros.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.LevyChannelSumSquares

/-- **The drop of a self-convolution is half a square integral.** -/
theorem selfConvolution_zero_sub {f : ℝ → ℝ} (hf : MemLp f 2 volume) (v : ℝ) :
    selfConvolution f 0 - selfConvolution f v
      = (1 / 2) * ∫ x : ℝ, (f x - f (x + v)) ^ 2 := by
  have hf2 : Integrable (fun x => f x ^ 2) volume := by
    simpa [sq] using hf.integrable_sq
  have hfv : MemLp (fun x => f (x + v)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume v)
  have hfv2 : Integrable (fun x => f (x + v) ^ 2) volume := by
    simpa [sq] using hfv.integrable_sq
  have hprod : Integrable (fun x => f x * f (x + v)) volume :=
    MemLp.integrable_mul hf hfv
  have hshift : ∫ x : ℝ, f (x + v) ^ 2 = ∫ x : ℝ, f x ^ 2 :=
    integral_add_right_eq_self (fun x => f x ^ 2) v
  have hsc0 : selfConvolution f 0 = ∫ x : ℝ, f x ^ 2 := by
    simp only [selfConvolution, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (sq (f x)).symm)
  have hexp : ∀ x, (f x - f (x + v)) ^ 2 = f x ^ 2 + f (x + v) ^ 2 - 2 * (f x * f (x + v)) := by
    intro x; ring
  have h12 : Integrable (fun x => f x ^ 2 + f (x + v) ^ 2) volume := hf2.add hfv2
  have h2p : Integrable (fun x => 2 * (f x * f (x + v))) volume := hprod.const_mul 2
  have hsplit : ∫ x : ℝ, (f x - f (x + v)) ^ 2
      = (∫ x : ℝ, f x ^ 2) + (∫ x : ℝ, f (x + v) ^ 2) - 2 * ∫ x : ℝ, f x * f (x + v) := by
    simp_rw [hexp]
    rw [integral_sub h12 h2p, integral_add hf2 hfv2, integral_const_mul]
  rw [hsplit, hshift, hsc0]
  simp only [selfConvolution]
  ring

/-- **A mode sum is square-integrable**: bounded, measurable, and supported on the window. -/
theorem memLp_modeSum {ι : Type*} [Fintype ι] (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    MemLp (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) 2 volume :=
  Cvs.Finite.ModeSumFormDomain.memLp_two_of_bounded (Cvs.Finite.ModeSumPairValues.measurable_modeSum L mode xi)
    (Cvs.Finite.ModeSumPairValues.abs_modeSum_le L mode xi)
    (fun _ hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L mode xi hs)

end Cvs.WeilForm.Archimedean.LevyChannelSumSquares
