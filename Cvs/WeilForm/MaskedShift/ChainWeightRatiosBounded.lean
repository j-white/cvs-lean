import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Cvs.WeilForm.MaskedShift.ChainArithmetic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

open Cvs.Operator

variable {β : ℝ}

/-! # B34: the weight ratios are bounded

The integrability side conditions of the Schur estimate reduce to one fact: the
chain weight is at most `1` and at least `sin(π/(m+1))`, so every ratio
`w(y)/w(x)` is bounded by `1/sin(π/(m+1))`.  Each integrand is then a bounded
multiple of `f²`, which is integrable since `f ∈ L²`.
-/

/-- The floor of the chain weight is strictly positive. -/
theorem sin_cap_pos (hβ : 0 < β) : 0 < Real.sin (π / ((cap 1 β : ℝ) + 1)) := by
  have hcap : 0 < cap 1 β := by
    unfold cap; rw [Nat.ceil_pos]; positivity
  have hc1 : (1 : ℝ) ≤ (cap 1 β : ℝ) := by exact_mod_cast hcap
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **Every weight ratio is bounded** by `1 / sin(π/(m+1))`. -/
theorem ratio_le (hβ : 0 < β) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    chainWeight β y / chainWeight β x ≤ 1 / Real.sin (π / ((cap 1 β : ℝ) + 1)) := by
  have hwx : 0 < chainWeight β x := chainWeight_pos β x hβ hx1
  have hlow := chainWeight_ge_cap β x hβ hx0 hx1
  have hspos := sin_cap_pos hβ
  rw [div_le_div_iff₀ hwx hspos]
  have h1 : chainWeight β y ≤ 1 := chainWeight_le_one β y
  nlinarith [hspos.le, hlow, h1]

end Cvs.Operator
