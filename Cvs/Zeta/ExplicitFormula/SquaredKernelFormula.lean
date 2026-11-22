import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit formula at the kernel the criterion pairs against

`an earlier result` proves Guinand–Weil for `gaussAmp`.
-/

namespace Cvs.Zeta.SquaredKernel

open Complex ArithmeticFunction

/-! ### Squaring a decay bound

The one arithmetic fact behind everything below: a nonnegative quantity bounded
by `A/d` with `d ≥ 1` has square bounded by `A²/d` — the extra factor `d` in the
denominator is discarded, keeping the exponent the caller asked for.
-/

/-! ### The squared kernel -/

/-! ### The formula -/

/-!
### The value at the pole of `ζ`

`Cvs.Detection.pole_channel_eq` evaluates the two pole integrals of the explicit formula outright:
their real parts sum to `2π·Re(ofCritical h 1)`, the residue this kernel picks up crossing `z
= 1`.
-/

/-!
### The Weil family is summable, unconditionally

Window exhaustion needs the zero side to converge, and it does — for elementary reasons, with
no RH and no zero-free region.
-/

/-- `y²/2 ≤ e^y` on `y ≥ 0`, from Mathlib's quadratic bound. -/
theorem sq_half_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 2 ≤ Real.exp y := by
  have h := Real.quadratic_le_exp_of_nonneg hy
  nlinarith [Real.exp_pos y]

/-- **The Gaussian ordinate bound beats the quartic weight**, with the loss
`1 + 8/λ²` and nothing else. -/
theorem exp_neg_le_quartic {lam : ℝ} (hlam : 0 < lam) (g : ℝ) :
    Real.exp (-(lam * g ^ 2 / 2)) ≤ (1 + 8 / lam ^ 2) * (1 / (1 + g ^ 4)) := by
  have hy : (0 : ℝ) ≤ lam * g ^ 2 / 2 := by positivity
  have hE : (0 : ℝ) < Real.exp (lam * g ^ 2 / 2) := Real.exp_pos _
  have hg : (0 : ℝ) < 1 + g ^ 4 := by positivity
  have h1 : (1 : ℝ) ≤ Real.exp (lam * g ^ 2 / 2) := Real.one_le_exp hy
  have hq : (lam * g ^ 2 / 2) ^ 2 / 2 ≤ Real.exp (lam * g ^ 2 / 2) := sq_half_le_exp hy
  have h8 : (8 / lam ^ 2) * ((lam * g ^ 2 / 2) ^ 2 / 2)
      ≤ (8 / lam ^ 2) * Real.exp (lam * g ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hid : (8 / lam ^ 2) * ((lam * g ^ 2 / 2) ^ 2 / 2) = g ^ 4 := by
    field_simp; ring
  rw [hid] at h8
  have hkey : (1 : ℝ) * (1 + g ^ 4) ≤ (1 + 8 / lam ^ 2) * Real.exp (lam * g ^ 2 / 2) := by
    nlinarith
  have hneg : Real.exp (-(lam * g ^ 2 / 2)) = 1 / Real.exp (lam * g ^ 2 / 2) := by
    rw [Real.exp_neg]; ring
  rw [hneg, mul_one_div, div_le_div_iff₀ hE hg]
  exact hkey

-- prose-lint-allow: R7 this file exists to supply the hypotheses Cvs.Zeta.ExplicitFormula.WeightedZeroSide consumes; naming them is the point

-- prose-lint-allow: R7 this file exists to supply the hypotheses Cvs.Zeta.ExplicitFormula.WeightedZeroSide consumes; naming them is the point

-- prose-lint-allow: R7 this file exists to supply the hypotheses Cvs.Zeta.ExplicitFormula.WeightedZeroSide consumes; naming them is the point

-- prose-lint-allow: R7 this file exists to supply the hypotheses Cvs.Zeta.ExplicitFormula.WeightedZeroSide consumes; naming them is the point

end Cvs.Zeta.SquaredKernel
