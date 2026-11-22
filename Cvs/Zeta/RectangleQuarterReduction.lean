import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiConj
import Cvs.Zeta.XiVertical

/-!
# The horizontals, and the quarter reduction without a branch
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.Zeta.RectangleQuarterReduction

/-- `conj (x + iT) = x - iT` for real `x`, `T`. -/
theorem conj_horiz (x T : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) = (x : ℂ) - (T : ℂ) * I := by
  apply Complex.ext <;> simp

/-- `conj (2 + iy) = 2 - iy`. -/
theorem conj_vert (y : ℝ) :
    (starRingEnd ℂ) ((2 : ℂ) + (y : ℂ) * I) = (2 : ℂ) - (y : ℂ) * I := by
  apply Complex.ext <;> simp

/-! ### The horizontals -/

/-- **The bottom edge is minus the top.**  `x - iT = 1 - ((1-x) + iT)`, and `x ↦ 1-x` maps
`[-1,2]` onto itself. -/
theorem bottom_eq_neg_top (T : ℝ) :
    (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) - (T : ℂ) * I))
      = - ∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I) := by
  set g : ℝ → ℂ := fun t => logDeriv riemannXi ((t : ℂ) + (T : ℂ) * I) with hg
  have hpt : ∀ x : ℝ,
      logDeriv riemannXi ((x : ℂ) - (T : ℂ) * I) = -(g (1 - x)) := by
    intro x
    have hc : ((x : ℂ) - (T : ℂ) * I) = 1 - ((((1 - x : ℝ)) : ℂ) + (T : ℂ) * I) := by
      push_cast; ring
    rw [hg]
    simp only
    rw [hc, logDeriv_riemannXi_one_sub]
  calc (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) - (T : ℂ) * I))
      = ∫ x in (-1 : ℝ)..2, -(g (1 - x)) := by simp_rw [hpt]
    _ = - ∫ x in (-1 : ℝ)..2, g (1 - x) := intervalIntegral.integral_neg
    _ = - ∫ x in (-1 : ℝ)..2, g x := by
        rw [intervalIntegral.integral_comp_sub_left g 1]
        norm_num

/-- **The top edge is purely imaginary.**  `conj H = -H`. -/
theorem conj_top (T : ℝ) :
    (starRingEnd ℂ) (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I))
      = - ∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  rw [show (fun x : ℝ => (starRingEnd ℂ) (logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)))
        = fun x : ℝ => logDeriv riemannXi ((x : ℂ) - (T : ℂ) * I) by
    funext x
    rw [← logDeriv_riemannXi_conj, conj_horiz]]
  exact bottom_eq_neg_top T

/-- `Re H = 0`, the scalar form of `conj_top`. -/
theorem re_top_eq_zero (T : ℝ) :
    (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)).re = 0 := by
  have h := conj_top T
  set H : ℂ := ∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)
  have : H.re = -H.re := by
    have := congrArg Complex.re h
    simpa using this
  linarith

/-! ### The verticals -/

/-- **The right edge is real.**  `conj V = V`. -/
theorem conj_vertical (T : ℝ) :
    (starRingEnd ℂ) (∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I))
      = ∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) := by
  set g : ℝ → ℂ := fun t => logDeriv riemannXi ((2 : ℂ) + (t : ℂ) * I) with hg
  rw [← intervalIntegral.intervalIntegral_conj]
  have hpt : ∀ y : ℝ,
      (starRingEnd ℂ) (logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)) = g (-y) := by
    intro y
    rw [← logDeriv_riemannXi_conj, conj_vert, hg]
    simp only
    congr 1
    push_cast; ring
  calc (∫ y in (-T)..T, (starRingEnd ℂ) (logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)))
      = ∫ y in (-T)..T, g (-y) := by simp_rw [hpt]
    _ = ∫ y in (-T)..T, g y := by
        rw [intervalIntegral.integral_comp_neg (a := -T) (b := T) g]
        norm_num

/-- `Im V = 0`, the scalar form of `conj_vertical`. -/
theorem im_vertical_eq_zero (T : ℝ) :
    (∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).im = 0 := by
  have h := conj_vertical T
  set V : ℂ := ∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)
  have : -V.im = V.im := by
    have := congrArg Complex.im h
    simpa using this
  linarith

/-! ### The halving of the top edge -/

/-- **The left half of the top edge is `-conj` of the right half.**  A substitution identity:
`x ↦ 1-x` maps `[½,2]` onto `[-1,½]`, and `ξ'/ξ((1-x)+iT) = -conj(ξ'/ξ(x+iT))`. -/
theorem left_half_eq_neg_conj (T : ℝ) :
    (∫ x in (-1 : ℝ)..(1/2 : ℝ), logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I))
      = - (starRingEnd ℂ)
          (∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) := by
  set g : ℝ → ℂ := fun t => logDeriv riemannXi ((t : ℂ) + (T : ℂ) * I) with hg
  have hpt : ∀ x : ℝ, g (1 - x) = -(starRingEnd ℂ) (g x) := by
    intro x
    have hc : ((((1 - x : ℝ)) : ℂ) + (T : ℂ) * I)
        = 1 - ((starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I)) := by
      rw [conj_horiz]; push_cast; ring
    rw [hg]
    simp only
    rw [hc, logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj]
  rw [show (∫ x in (-1 : ℝ)..(1/2 : ℝ), logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I))
        = ∫ x in (-1 : ℝ)..(1/2 : ℝ), g x from rfl]
  rw [show (∫ x in (-1 : ℝ)..(1/2 : ℝ), g x)
        = ∫ x in (1/2 : ℝ)..2, g (1 - x) by
    rw [intervalIntegral.integral_comp_sub_left g 1]
    norm_num]
  simp_rw [hpt]
  rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

/-! ### The assembly -/

/-!
### Halving the top edge

The only step in this file that is not a pointwise identity or a substitution.
-/

open MeasureTheory in
/-- **The top edge, halved.**  `H = B − conj B` with `B` over `Re ∈ [½,2]`. -/
theorem top_eq_half_sub_conj (T : ℝ)
    (hL : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) volume (-1) (1/2))
    (hR : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) volume (1/2) 2) :
    (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I))
      = (∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I))
        - (starRingEnd ℂ)
            (∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR, left_half_eq_neg_conj]
  ring

open MeasureTheory in
/-- `Im H = 2·Im B`: the top edge's imaginary part is carried entirely by `Re ∈ [½,2]`. -/
theorem im_top_eq_two_im_half (T : ℝ)
    (hL : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) volume (-1) (1/2))
    (hR : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)) volume (1/2) 2) :
    (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)).im
      = 2 * (∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T : ℂ) * I)).im := by
  rw [top_eq_half_sub_conj T hL hR]
  simp
  ring

end Cvs.Zeta.RectangleQuarterReduction
