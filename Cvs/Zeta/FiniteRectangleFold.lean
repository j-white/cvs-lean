import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical

/-!
# Folding the two verticals of the finite rectangle
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.ZeroCounting

/-- The left edge of the rectangle, folded onto the right edge.  Finite-interval companion to
`Cvs.Zeta.integral_vline_left_eq_neg`. -/
theorem integral_vline_left_eq_neg_finite (T : ℝ) :
    (∫ y in (-T)..T, logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I))
      = - ∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) := by
  set g : ℝ → ℂ := fun t => logDeriv riemannXi ((2 : ℂ) + (t : ℂ) * I) with hg
  have hpt : ∀ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I) = -(g (-y)) := by
    intro y
    have hc : ((-1 : ℂ) + (y : ℂ) * I) = 1 - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [hg]
    simp only
    rw [hc, logDeriv_riemannXi_one_sub]
  calc (∫ y in (-T)..T, logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I))
      = ∫ y in (-T)..T, -(g (-y)) := by simp_rw [hpt]
    _ = - ∫ y in (-T)..T, g (-y) := intervalIntegral.integral_neg
    _ = - ∫ y in (-T)..T, g y := by
        rw [intervalIntegral.integral_comp_neg (a := -T) (b := T) g]
        norm_num

end Cvs.ZeroCounting
