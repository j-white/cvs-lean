import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped InnerProductSpace NNReal

namespace Cvs.PrimeOperator


/-!
# The pairing is against a Weil test function

`testFn c f` was defined as the self-convolution of the lift *read in the scale `log c`* — a
displacement of `u` in the explicit formula is a rotation of `u / log c` on the circle.
-/

/-- **Rescaling a self-convolution.** Nothing here is about `lift`: for any `h` and any positive
`L`, dividing the argument by `L` and the value by `√L` gives a function whose
self-convolution is `h`'s, read at `t/L`. -/
theorem selfConvolution_rescale {L : ℝ} (hL : 0 < L) (h : ℝ → ℝ) (t : ℝ) :
    selfConvolution (fun y => h (y / L) / Real.sqrt L) t = selfConvolution h (t / L) := by
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  calc selfConvolution (fun y => h (y / L) / Real.sqrt L) t
      = ∫ x : ℝ, (fun y => h y * h (y + t / L) / L) (x / L) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [show (x + t) / L = x / L + t / L by ring, div_mul_div_comm, hsq]
    _ = |L| • ∫ y : ℝ, h y * h (y + t / L) / L :=
        MeasureTheory.Measure.integral_comp_div
          (fun y : ℝ => h y * h (y + t / L) / L) L
    _ = selfConvolution h (t / L) := by
        rw [abs_of_pos hL, smul_eq_mul, integral_div]
        unfold selfConvolution
        field_simp

end Cvs.PrimeOperator
