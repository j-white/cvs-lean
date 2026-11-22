import Mathlib
import Cvs.Xi.PhiHalfLineMoments
import Cvs.Xi.RiemannPhiKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail of `Φ` past the window's edge

The edge bound leaves a decay faster than the plain exponential, so the mass of `Φ` beyond a
point is at most a constant times the plain exponential there. This is the quantity an aliasing
estimate has to control, since the frequencies the grid cannot resolve are carried by exactly
this tail.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.PhiTailPastEdge

open Cvs.Xi.RiemannPhiKernel

theorem one_le_decayRate : 1 ≤ Cvs.Xi.PhiHalfLineMoments.decayRate := by
  have h := Real.pi_gt_three
  unfold Cvs.Xi.PhiHalfLineMoments.decayRate
  linarith

/-- The constant of the tail bound. -/
theorem tailConst_nonneg : 0 ≤ phiBoundConst * exp (-π) :=
  mul_nonneg Cvs.Xi.PhiHalfLineMoments.phiBoundConst_nonneg (Real.exp_pos _).le

/-- **`Φ` is below a plain decaying exponential on the half line.** -/
theorem riemannPhi_le_exp_one {u : ℝ} (hu : 0 ≤ u) :
    riemannPhi u ≤ (phiBoundConst * exp (-π)) * exp (-u) := by
  refine (Cvs.Xi.PhiHalfLineMoments.riemannPhi_le_exp hu).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) tailConst_nonneg
  nlinarith [one_le_decayRate, hu]

end Cvs.Xi.PhiTailPastEdge
