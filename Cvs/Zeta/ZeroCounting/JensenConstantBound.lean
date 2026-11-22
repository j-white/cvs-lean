import Mathlib
import Cvs.Zeta.ZeroCounting.JensenChainConstants
import Cvs.Zeta.ZeroCounting.JensenGrowthConstant
import Cvs.Zeta.ZetaZeroWindows

/-!
# The Jensen constant, bounded

`completedXiCore s = s(s−1)Λ₀(s) + 1`, so at `s = 2` it is `2Λ₀(2) + 1` and the strip bound
pins it near `1`.  No evaluation of `‖completedXiCore 2‖` is needed after all, and with `K`
from `Cvs.Zeta.ZeroCounting.JensenGrowthConstant` the Jensen constant is a number.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Real Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.ZeroCounting.JensenConstantBound
open Cvs.ZeroFree

/-- **`‖completedXiCore 2‖` is within `2/36.3` of `1`.**  The `+1` in the definition is the
whole of it: the other term is `2Λ₀(2)`, and `Cvs.Zeta.ThetaTailSquared` bounds `Λ₀` on this very strip. -/
theorem norm_completedXiCore_two_bounds :
    1 - 2/36.3 ≤ ‖completedXiCore 2‖ ∧ ‖completedXiCore 2‖ ≤ 1 + 2/36.3 := by
  have hL : ‖completedRiemannZeta₀ 2‖ ≤ 1 / 36.3 :=
    Cvs.Zeta.ZeroCounting.JensenChainConstants.norm_completedRiemannZeta₀_le_strip_num
      (by norm_num) (by norm_num)
  have hval : completedXiCore 2 = 2 * completedRiemannZeta₀ 2 + 1 := by
    rw [completedXiCore]; ring
  have h2 : ‖(2 : ℂ) * completedRiemannZeta₀ 2‖ ≤ 2 / 36.3 := by
    rw [norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    linarith
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-((2 : ℂ) * completedRiemannZeta₀ 2))
    rw [norm_neg] at this
    have hrw : (1 : ℂ) - -((2 : ℂ) * completedRiemannZeta₀ 2)
        = 2 * completedRiemannZeta₀ 2 + 1 := by ring
    rw [hrw, show ‖(1:ℂ)‖ = 1 by norm_num] at this
    rw [hval]
    linarith
  · have := norm_add_le ((2 : ℂ) * completedRiemannZeta₀ 2) 1
    rw [show ‖(1:ℂ)‖ = 1 by norm_num] at this
    rw [hval]
    linarith

/-- The logarithm of that, without evaluating a logarithm: `log x ≤ x − 1` upward, and the
same applied to `x⁻¹` downward. -/
theorem abs_log_norm_completedXiCore_two_le :
    |Real.log ‖completedXiCore 2‖| ≤ 0.0584 := by
  obtain ⟨hlo, hhi⟩ := norm_completedXiCore_two_bounds
  have hx0 : (0:ℝ) < ‖completedXiCore 2‖ := by
    refine lt_of_lt_of_le ?_ hlo
    norm_num
  have hup : Real.log ‖completedXiCore 2‖ ≤ 0.0584 := by
    refine le_trans (Real.log_le_sub_one_of_pos hx0) ?_
    linarith
  have hxinv : (‖completedXiCore 2‖)⁻¹ ≤ 1.0584 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]
    norm_num
    linarith
  have hdown := Real.log_le_sub_one_of_pos (x := (‖completedXiCore 2‖)⁻¹) (by positivity)
  rw [Real.log_inv] at hdown
  rw [abs_le]
  constructor <;> linarith

/-- **`|log K| + |log ‖ξ₂‖| ≤ 0.71`.**  `K = π²/6 > 1`, so `log K ≤ K − 1`. -/
theorem jensenD_le :
    |Real.log (Real.pi ^ 2 / 6)| + |Real.log ‖completedXiCore 2‖| ≤ 0.71 := by
  have hK1 : (1:ℝ) ≤ Real.pi ^ 2 / 6 := Cvs.Zeta.ZeroCounting.JensenGrowthConstant.one_le_zetaTwo
  have hKu : Real.pi ^ 2 / 6 ≤ 1.645 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hlog : Real.log (Real.pi ^ 2 / 6) ≤ 0.645 :=
    le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hlog0 : 0 ≤ Real.log (Real.pi ^ 2 / 6) := Real.log_nonneg hK1
  rw [abs_of_nonneg hlog0]
  linarith [abs_log_norm_completedXiCore_two_le]

end Cvs.Zeta.ZeroCounting.JensenConstantBound
