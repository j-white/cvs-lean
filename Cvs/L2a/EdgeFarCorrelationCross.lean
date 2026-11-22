import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge–far correlation from a cross bound charged to the tail norm

With `N = e + f + 2x` (`e = ∫F_e²`, `f = ∫F_f²`, `x = ∫F_eF_f`), a bound `|x| ≤ C·N` with `C < 1/4` gives
`−(r(e + f)) ≤ 2x` for `r = 2C/(1 − 2C) < 1`: the correlation hypothesis of the plateau (Cvs.L2a.FarMassPlateau at `w = 1`) from a
cross bound on the tail norm itself, as the trivial gain of Cvs.L2a.TrivialGainAdditiveCross.
-/

namespace Cvs.L2a.EdgeFarCorrelationCross

/-- **The correlation from an additive cross bound.** -/
theorem corr_of_cross {e f x N C : ℝ} (hN : N = e + f + 2 * x) (hC0 : 0 ≤ C)
    (hC : C < 1 / 4) (hx : |x| ≤ C * N) :
    -((2 * C / (1 - 2 * C)) * (e + f)) ≤ 2 * x := by
  have h2 : 0 < 1 - 2 * C := by linarith
  have hlow : -(C * N) ≤ x := by linarith [neg_abs_le x]
  have hup : x ≤ C * N := le_trans (le_abs_self x) hx
  have hN' : (1 - 2 * C) * N ≤ e + f := by nlinarith
  have key : 2 * C * N ≤ 2 * C / (1 - 2 * C) * (e + f) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]; nlinarith
  linarith

/-- The correlation constant is below 1 exactly when `C < 1/4`. -/
theorem corr_const_lt_one {C : ℝ} (hC : C < 1 / 4) : 2 * C / (1 - 2 * C) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

end Cvs.L2a.EdgeFarCorrelationCross
