import Mathlib
import Cvs.Xi.RiemannPhiKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The moments of `Φ` on the half line

The edge bound carries a growing exponential against a doubly exponential decay. Bounding the
inner exponential below by its tangent line at the origin turns the pair into a single decaying
exponential, which dominates every power of the variable, so each moment of `Φ` converges.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.PhiHalfLineMoments

open Cvs.Xi.RiemannPhiKernel

/-- The decay the edge bound leaves once the growing factor is absorbed. -/
def decayRate : ℝ := 2 * π - 9 / 2

theorem phiBoundConst_nonneg : 0 ≤ phiBoundConst := by
  unfold phiBoundConst
  have h : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * exp (-(π * ((n : ℝ) + 1) ^ 2)) :=
    tsum_nonneg (fun n => by positivity)
  exact mul_nonneg (by positivity) h

/-- **The edge bound as a single decaying exponential.** -/
theorem riemannPhi_le_exp {u : ℝ} (hu : 0 ≤ u) :
    riemannPhi u ≤ (phiBoundConst * exp (-π)) * exp (-(decayRate * u)) := by
  refine (riemannPhi_le hu).trans ?_
  have hpi := Real.pi_pos
  have hexp : (2 : ℝ) * u + 1 ≤ exp (2 * u) := by
    have := Real.add_one_le_exp (2 * u); linarith
  have h1 : exp (-(π * exp (2 * u))) ≤ exp (-(π * (2 * u + 1))) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hfac : exp (9 * u / 2) * exp (-(π * (2 * u + 1)))
      = exp (-π) * exp (-(decayRate * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    unfold decayRate
    congr 1
    ring
  calc phiBoundConst * exp (9 * u / 2) * exp (-(π * exp (2 * u)))
      ≤ phiBoundConst * exp (9 * u / 2) * exp (-(π * (2 * u + 1))) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg phiBoundConst_nonneg (Real.exp_pos _).le)
    _ = (phiBoundConst * exp (-π)) * exp (-(decayRate * u)) := by
        rw [mul_assoc, hfac, ← mul_assoc]

end Cvs.Xi.PhiHalfLineMoments
