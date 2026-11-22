import Mathlib
import Cvs.Xi.MellinWeightEndpoint
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.ThetaTransformLogForm

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta transform in the completed zeta's shape

The substitution left the weight as a reciprocal times a fourth root, and the completed zeta
carries it as a power. They are the same number, so the two integrals are the same integral, and
the theta transform can be read in the shape the completed zeta produces.
-/

noncomputable section

open Set MeasureTheory Real

namespace Cvs.Xi.ThetaTransformCompletedShape

open Cvs.Xi.PhiKernelIdentitySums

/-- **The theta transform, written as the completed zeta writes it.** -/
theorem integral_thetaSum_cos_rpow (τ : ℝ) :
    ∫ u in Ioi (0 : ℝ), thetaSum u * Real.cos (τ * u)
      = (1 / 4) * ∫ x in Ioi (1 : ℝ),
          x ^ (-3 / 4 : ℝ) * Real.cos (τ / 2 * Real.log x)
            * (HurwitzZeta.evenKernel 0 x - 1) := by
  rw [Cvs.Xi.ThetaTransformLogForm.integral_thetaSum_cos_eq τ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  rw [Cvs.Xi.MellinWeightEndpoint.weight_rpow_eq hx0]
  ring

end Cvs.Xi.ThetaTransformCompletedShape
