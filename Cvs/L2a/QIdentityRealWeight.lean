import Mathlib
import Cvs.L2a.FarIntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Q-identity on any interval with any `C²` weight

For `c, y > 0`, a rung `ψ = psi c g` and a `C²` weight `w` on `[α, β] ⊆ (1, ∞)`: `∫_α^β wψe = ∫_α^β eψR + [B]_α^β`
with `e = e^{icxy}`, `Q = c²(x² − 1)(y² − 1) − (c² − χ) − 2icxy ≠ 0`, `G = w/Q`, `R = (pG′)′ + 2icy pG′`; and its real part.
-/

namespace Cvs.L2a.QIdentityRealWeight

open Real Set Filter Topology MeasureTheory intervalIntegral Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts

/-! ### `Q` does not vanish -/

/-- `Im Q = −2cxy`. -/
theorem qQ_im (c χ y x : ℝ) : (qQ c χ y x).im = -(2 * c * x * y) := by
  simp only [qQ, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `Q ≠ 0` for `c, x, y > 0`, from `Im Q = −2cxy`, any `χ`. -/
theorem qQ_ne_zero_of_pos {c χ y x : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) : qQ c χ y x ≠ 0 := by
  intro h
  have := qQ_im c χ y x
  rw [h, Complex.zero_im] at this
  nlinarith [mul_pos (mul_pos hc hx) hy]

/-! ### Continuity on a set -/

/-! ### The identity on `[α, β]` -/

end Cvs.L2a.QIdentityRealWeight
