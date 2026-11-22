import Mathlib
import Cvs.Prolate.EndpointLadderLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.QuarticEndpointLadder
import Cvs.Prolate.SepticLevelComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The q-side over the floor decays like `x^{−5/2} log x`

From `QuarticEndpointLadder`'s `C c⁴ h₄(1)² ≤ h₈(1)²` (`C = C_law e^{−73}`, `c = 2πx`): the ratio of the q-side scale times `c K`,
`K = √x log x`, to the floor scale is `c K h₄(1)²/h₈(1)² ≤ log x/(C(2π)³x^{5/2})`, and it tends to `0`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.EvenRungsByIndex

namespace Cvs.L2a.QSideOverFloorDecay
open Cvs.ZeroCounting

/-- The quartic-law constant `C = C_law e^{−73}`. -/
def C4 : ℝ := Cvs.Prolate.EndpointLadderLaw.lawC * exp (-73)

theorem C4_pos : 0 < C4 := by unfold C4; have := Cvs.Prolate.EndpointLadderLaw.lawC_pos; positivity

/-- **The decay bound**: at `c = 2πx`, `x ≥ 80`,
`c (√x log x) h₄(1)²/h₈(1)² ≤ log x/(C (2π)³ x²√x)`. -/
theorem ratio_le (x : ℕ) (hx : 80 ≤ x) :
    2 * π * x * (√x * log x) * rung (2 * π * x) 2 1 ^ 2 / rung (2 * π * x) 4 1 ^ 2
      ≤ log x / (C4 * (2 * π) ^ 3 * ((x : ℝ) ^ 2 * √x)) := by
  have hx' : (80 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set c := 2 * π * (x : ℝ) with hcd
  have hc0 : 0 < c := by positivity
  have h4 : ∃ χ, IsLevelIdx c 4 χ :=
    Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by rw [hcd]; nlinarith [Real.pi_lt_d2, Real.pi_gt_three])
      le_rfl
  have hψ8 : 0 < rung c 4 1 ^ 2 := by have := rung_one_ne_zero h4; positivity
  have hq := Cvs.Prolate.QuarticEndpointLadder.ladder_quartic x hx
  rw [← hcd, show c ^ (4 : ℝ) = c ^ 4 by norm_cast] at hq
  have hlog : 0 ≤ log (x : ℝ) := Real.log_nonneg (by linarith)
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  have hsx2 : √(x : ℝ) ^ 2 = x := Real.sq_sqrt hx0.le
  have hC := C4_pos
  rw [div_le_div_iff₀ hψ8 (by positivity)]
  -- `ψ₄² ≤ ψ₈²/(C c⁴)`
  have h1 : rung c 2 1 ^ 2 * (C4 * c ^ 4) ≤ rung c 4 1 ^ 2 := by unfold C4; linarith
  have e : 2 * π * x * (√x * log x) * rung c 2 1 ^ 2 * (C4 * (2 * π) ^ 3 * ((x : ℝ) ^ 2 * √x))
      = log x * (√x ^ 2 * (rung c 2 1 ^ 2 * (C4 * c ^ 4))) / x := by
    rw [hcd]; field_simp
  rw [e, hsx2, div_le_iff₀ hx0]
  have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ log (x : ℝ) * x by positivity)
  nlinarith

end Cvs.L2a.QSideOverFloorDecay
