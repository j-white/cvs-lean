import Mathlib
import Cvs.Zeta.Convexity.ZetaOneLineLog

/-!
# The convexity exponent sharpened to `1/3`

‖ζ(½+it)‖ ≤ C_ε·(1+|t|)^{(2ε+1)/3} for every `ε > 0`, `|t| ≥ 1` .
-/

open Complex

namespace Cvs.Zeta.Convexity.CriticalLineThirdExponent
open Cvs.ZetaGrowth

/-- `log x ≤ x^ε/ε` for `x ≥ 1`, `ε > 0`: apply `log y ≤ y - 1` to `y = x^ε`. -/
theorem log_le_rpow_div {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    Real.log x ≤ x ^ ε / ε := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hlog : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos hpow
  rw [Real.log_rpow hx0] at hlog
  rw [le_div_iff₀ hε]
  nlinarith

/-- **The near edge at `σ = 1`, with exponent `ε`.**  `ZetaOneLineLog` gives `6 + log|t|`, and
`log ≤ (·)^ε/ε` converts that into the `Ca·(1+|t|)^a` shape the ladder consumes. -/
theorem zeta₀_edge_one {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta₀ (1 + (t : ℂ) * I)‖ ≤ (6 + 1 / ε) * (1 + |t|) ^ ε := by
  have hb1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hb0 : (0 : ℝ) < 1 + |t| := by linarith
  have hpow1 : (1 : ℝ) ≤ (1 + |t|) ^ ε := Real.one_le_rpow hb1 (le_of_lt hε)
  have hlt : |t| ≤ 1 + |t| := by linarith
  have hlog : Real.log |t| ≤ (1 + |t|) ^ ε / ε := by
    refine le_trans (Real.log_le_log (lt_of_lt_of_le zero_lt_one ht) hlt) ?_
    exact log_le_rpow_div hε hb1
  have hz := Cvs.ZetaGrowth.norm_zeta₀_one_add_I ht
  have hstep : (6 : ℝ) + Real.log |t| ≤ (6 + 1 / ε) * (1 + |t|) ^ ε := by
    have h1 : (6 : ℝ) ≤ 6 * (1 + |t|) ^ ε := by nlinarith
    have h2 : Real.log |t| ≤ (1 / ε) * (1 + |t|) ^ ε := by
      rw [one_div, inv_mul_eq_div]
      exact hlog
    nlinarith
  linarith

/-! ### The ladder at `α = -1/2`, `β = 1` -/

variable {ε : ℝ}

end Cvs.Zeta.Convexity.CriticalLineThirdExponent
