import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The derivative kernel is a divided difference

`ψ'` is odd, bounded by the weight total, and its two-point quotient is exactly the divided
difference the CvS matrix is built from.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset

namespace Cvs.Finite.DerivativeKernelDividedDifference

variable {ι : Type*}

/-- **CvS's `ψ` for a purely atomic `𝒟`**: atoms of weight `w j` at `u j ∈ [0, L]`. -/
def psiPrime (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.pi) * ∑ j ∈ s, w j * Real.sin (2 * Real.pi * x * (1 - u j / L))

/-! ### Oddness -/

/-- **`ψ` is odd.**  CvS's `(form)` asks for `b_{−i} = −b_i`; this is that fact. -/
theorem psiPrime_neg (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (x : ℝ) :
    psiPrime L s w u (-x) = -psiPrime L s w u x := by
  unfold psiPrime
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [show 2 * Real.pi * -x * (1 - u j / L) = -(2 * Real.pi * x * (1 - u j / L)) by ring,
    Real.sin_neg, mul_neg]

/-! ### Sum-to-product -/

/-- **Sum-to-product**, in the shape the divided difference wants: for a single atom with
angular frequency `t`, `sin(t·m) − sin(t·n) = 2 cos(t(m+n)/2) sin(t(m−n)/2)`. -/
theorem sin_mul_sub_sin_mul (t m n : ℝ) :
    Real.sin (t * m) - Real.sin (t * n)
      = 2 * Real.cos (t * (m + n) / 2) * Real.sin (t * (m - n) / 2) := by
  rw [Real.sin_sub_sin, show (t * m - t * n) / 2 = t * (m - n) / 2 by ring,
    show (t * m + t * n) / 2 = t * (m + n) / 2 by ring]
  ring

/-! ### The divided difference -/

/-- **The divided difference of `ψ`, in closed form.**  This is the off-diagonal entry
`q_{m,n}` of `matrixcomp` for a purely atomic `𝒟`: no cancellation is left, the `(m − n)`
in the denominator sits against a `sin(π(1 − u_j/L)(m − n))` that vanishes with it. -/
theorem psiPrime_divided_difference (L : ℝ) (s : Finset ι) (w u : ι → ℝ) {m n : ℝ}
    (hmn : m ≠ n) :
    (psiPrime L s w u m - psiPrime L s w u n) / (m - n)
      = (1 / Real.pi) * ∑ j ∈ s,
          w j * (2 * Real.cos (Real.pi * (1 - u j / L) * (m + n))
                   * Real.sin (Real.pi * (1 - u j / L) * (m - n)) / (m - n)) := by
  have hd : m - n ≠ 0 := sub_ne_zero.mpr hmn
  unfold psiPrime
  rw [← mul_sub, ← Finset.sum_sub_distrib, mul_div_assoc, Finset.sum_div]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  have key : Real.sin (2 * Real.pi * m * (1 - u j / L))
      - Real.sin (2 * Real.pi * n * (1 - u j / L))
      = 2 * Real.cos (Real.pi * (1 - u j / L) * (m + n))
          * Real.sin (Real.pi * (1 - u j / L) * (m - n)) := by
    have h := sin_mul_sub_sin_mul (2 * Real.pi * (1 - u j / L)) m n
    rw [show 2 * Real.pi * (1 - u j / L) * m = 2 * Real.pi * m * (1 - u j / L) by ring,
      show 2 * Real.pi * (1 - u j / L) * n = 2 * Real.pi * n * (1 - u j / L) by ring,
      show 2 * Real.pi * (1 - u j / L) * (m + n) / 2 = Real.pi * (1 - u j / L) * (m + n) by ring,
      show 2 * Real.pi * (1 - u j / L) * (m - n) / 2 = Real.pi * (1 - u j / L) * (m - n) by
        ring] at h
    exact h
  rw [← mul_sub, key, mul_div_assoc]

/-! ### A crude bound -/

/-- **`ψ` is bounded by its total mass**, uniformly in `x`, `u` and `L`. -/
theorem abs_psiPrime_le (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (x : ℝ) :
    |psiPrime L s w u x| ≤ (1 / Real.pi) * ∑ j ∈ s, |w j| := by
  have hpi : (0:ℝ) < 1 / Real.pi := by positivity
  unfold psiPrime
  rw [abs_mul, abs_of_pos hpi]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

end Cvs.Finite.DerivativeKernelDividedDifference
