import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityEvenBranch

/-!
# The scale comparison on the even branch
-/

open Complex

namespace Cvs.ArchScore

theorem evenLog_re (c K : ℝ) (s : ℂ) :
    (Cvs.ArchScore.evenLog c K s).re = Real.log ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ / 2 := by
  rw [Cvs.ArchScore.evenLog]
  simp [Complex.log_re]

/-- `‖K - (s+c)²‖ ≥ (Im s)²`, so its square root dominates the height. -/
theorem norm_ge_sq {c K β : ℝ} (hK : (β + c) ^ 2 < K) {s : ℂ}
    (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) :
    s.im ^ 2 ≤ ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Cvs.ArchScore.arg_re]
  nlinarith [sq_nonneg (s.re + c), hK, sq_nonneg (β + c)]

/-- **The height scale, on the even branch.**.rpow_ratio_le` for `‖K-(s+c)²‖^{a/2}`. -/
theorem rpow_ratio_even {c K β a : ℝ} (hK : (β + c) ^ 2 < K) (ha : 0 ≤ a) {s : ℂ}
    (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) (him : 1 ≤ |s.im|) :
    (1 + |s.im|) ^ a ≤ 2 ^ a * ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ ^ (a / 2) := by
  have hsq := norm_ge_sq hK hc hβ
  have habs : s.im ^ 2 = |s.im| ^ 2 := (sq_abs s.im).symm
  have hnn : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hpow : |s.im| ^ a ≤ ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ ^ (a / 2) := by
    have hid : ((|s.im| ^ (2 : ℕ) : ℝ)) ^ (a / 2) = |s.im| ^ a := by
      rw [← Real.rpow_natCast |s.im| 2, ← Real.rpow_mul hnn]
      congr 1
      push_cast
      ring
    rw [← hid]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [← habs]; exact hsq
  have h2 : (1 : ℝ) + |s.im| ≤ 2 * |s.im| := by linarith
  calc (1 + |s.im|) ^ a ≤ (2 * |s.im|) ^ a := Real.rpow_le_rpow (by linarith) h2 ha
    _ = 2 ^ a * |s.im| ^ a := Real.mul_rpow (by norm_num) hnn
    _ ≤ 2 ^ a * ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ ^ (a / 2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end Cvs.ArchScore
