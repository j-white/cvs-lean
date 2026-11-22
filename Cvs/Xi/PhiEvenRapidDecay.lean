import Mathlib
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.PhiTailPastEdge
import Cvs.Xi.RiemannPhiKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even extension decays faster than any power

`Φ` is below a decaying exponential on the half line and takes the same value at a point and its
reflection, so the even extension is below the exponential of minus the distance to the origin.
That exponential falls below any negative power at each end of the line, and the two ends are
what the cocompact filter sees.
-/

noncomputable section

open Real Set Filter Asymptotics

namespace Cvs.Xi.PhiEvenRapidDecay

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiTailPastEdge Cvs.Xi.PhiEvenExtension

/-- The even extension is below a decaying exponential in the distance to the origin. -/
theorem norm_phiEven_le (x : ℝ) :
    ‖phiEven x‖ ≤ (phiBoundConst * exp (-π)) * exp (-|x|) := by
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hpos := riemannPhi_pos habs
  have hnorm : ‖phiEven x‖ = riemannPhi |x| := by
    simp only [phiEven, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hpos
  rw [hnorm]
  exact riemannPhi_le_exp_one habs

end Cvs.Xi.PhiEvenRapidDecay
