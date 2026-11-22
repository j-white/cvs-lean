import Mathlib
import Cvs.Xi.EWindowReciprocalContraction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Reciprocal branch products and window selfadjointness

Reciprocal branch products are rational dilations with their exact interval gates,
and the finite E-window has a symmetric physical Lebesgue pairing.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.ReciprocalBranchSelfAdjoint
open Cvs.ZeroCounting

open Cvs.Xi.EWindowReciprocalContraction (branch)
open Cvs.Xi.EImageWindowPoisson (window)

/-- The physical Lebesgue pairing of one reciprocal branch is symmetric. -/
theorem integral_branch_mul {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (G H : ℝ → ℝ) :
    ∫ θ, branch a n G θ * H θ = ∫ θ, G θ * branch a n H θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  rw [show (fun θ => branch a n G θ * H θ) =
    (Icc ((n : ℝ) * a) 1).indicator
      (fun θ => a / θ * G ((n : ℝ) * a / θ) * H θ) by
        funext θ
        exact (indicator_mul_left _ _ _).symm,
    show (fun θ => G θ * branch a n H θ) =
      (Icc ((n : ℝ) * a) 1).indicator
        (fun θ => G θ * (a / θ * H ((n : ℝ) * a / θ))) by
          funext θ
          exact (indicator_mul_right _ _ _).symm]
  rw [integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    Cvs.Xi.EWindowReciprocalContraction.integral_branch_recip hb]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  ring

end Cvs.Xi.ReciprocalBranchSelfAdjoint
