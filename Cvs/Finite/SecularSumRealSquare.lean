import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# From `z²` real to `z` real, on the secular sum

    (z²).im = 0,  ∑ₙ aₙ/(z² − ωₙ²) = 0,  aₙ ≥ 0 not all zero   ⟹   z.im = 0

At a purely imaginary `z` every denominator `z² − ω²` is negative, so a sum with nonnegative
numerators is strictly negative and cannot vanish.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Finset

namespace Cvs.Finite.SecularSumRealSquare

/-- If `z²` is real and `z` is not, then `z` is purely imaginary. -/
theorem re_eq_zero_of_sq_im (z : ℂ) (hsq : (z ^ 2).im = 0) (him : z.im ≠ 0) : z.re = 0 := by
  have h : 2 * z.re * z.im = 0 := by
    have : (z ^ 2).im = 2 * z.re * z.im := by
      simp [pow_two, Complex.mul_im]; ring
    linarith [this ▸ hsq]
  rcases mul_eq_zero.mp h with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · norm_num at h3
    · exact h4
  · exact absurd h2 him

-- SCOPE OF `hnn`: in `Cvs.Limit.TransformZeroRealBridge`'s use, `a n` is the approximant's COSINE COEFFICIENT --
-- `Cvs.Finite.WindowCosineSumTransform`'s factorisation leaves it bare and `Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum` is `∑ a n cos(2πn x/L)`. So this
-- is nonnegativity in the coefficient basis, which is Parseval-different from pointwise
-- nonnegativity of the eigenfunction and from `an earlier result`/`an earlier result`'s nonnegativity at nodes:
-- `a₁ = 1` is coefficient-nonnegative but not pointwise, `1 − cos/2` is the converse.

end Cvs.Finite.SecularSumRealSquare
