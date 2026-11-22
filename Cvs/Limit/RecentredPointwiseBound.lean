import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformEven
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.RecentredDiagonalBound
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Upstream.OffAxesDense

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pointwise bound on the whole plane

Every lattice point is real, so a point off both axes is off the lattice, and a non-zero point
whose square is purely imaginary is off both axes.  The bound of `Cvs.Limit.RecentredDiagonalBound` therefore holds for every
`z` off the axes, and both of its sides are continuous, so it holds for every `z`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Polynomial Real

namespace Cvs.Limit.RecentredPointwiseBound
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity Cvs.Finite.ReducedSecularPolynomial
open Cvs.Finite.SecularCoefficientLimits Cvs.Limit.MomentSpineAlone

theorem sq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
  rw [sq, Complex.mul_im]; ring

/-- **Off the axes the square is not zero.** -/
theorem sq_ne_zero_of_offAxes {z : ℂ} (hz : z ∈ offAxes) : z ^ 2 ≠ 0 := by
  intro h
  have him : (z ^ 2).im = 0 := by rw [h]; rfl
  rw [sq_im] at him
  rcases mul_eq_zero.mp him with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · exact hz.1 h2
  · exact hz.2 h1

/-- **Off the axes no squared frequency is met**, the squared frequencies being real. -/
theorem qf_sub_sq_ne_zero {L : ℝ} (N : ℕ) (j : Fin N) {z : ℂ} (hz : z ∈ offAxes) :
    (qf L N j : ℂ) - z ^ 2 ≠ 0 := by
  intro h
  have hq : (qf L N j).im = 0 := by
    unfold qf
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  have him : ((qf L N j : ℂ) - z ^ 2).im = 0 := by rw [h]; rfl
  rw [Complex.sub_im, hq, sq_im] at him
  have h0 : 2 * z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · exact hz.1 h2
  · exact hz.2 h1

/-- **A non-zero point whose square is purely imaginary lies off both axes.** -/
theorem offAxes_of_sq_re_zero {w : ℂ} (hw : w ≠ 0) (hre : (w ^ 2).re = 0) : w ∈ offAxes := by
  have h : w.re * w.re - w.im * w.im = 0 := by rw [sq, Complex.mul_re] at hre; exact hre
  constructor
  · intro h0
    rw [h0] at h
    have him : w.im = 0 := by nlinarith [mul_self_nonneg w.im]
    exact hw (Complex.ext h0 him)
  · intro h0
    rw [h0] at h
    have hr : w.re = 0 := by nlinarith [mul_self_nonneg w.re]
    exact hw (Complex.ext hr h0)

/-- **The pointwise bound at every point of the plane**, normalised at a non-zero point whose
square is purely imaginary. -/
theorem norm_cgtransform_le (P R : ℕ) {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N) {w₀ : ℂ}
    (hw : w₀ ≠ 0) (hw₀ : (w₀ ^ 2).re = 0) (z : ℂ) :
    ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖
        * ‖w₀ ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
      ≤ ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖
        * ‖z ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
        * exp (‖z ^ 2‖ * ((shiftP (secPolyP L N (ground P R L hL N))).roots.map
            fun r => ‖r‖⁻¹).sum)
        * exp (‖z * L / (2 * π)‖ ^ 2 / N) := by
  have hwoff : w₀ ∈ offAxes := offAxes_of_sq_re_zero hw hw₀
  have hcont : Continuous (Cvs.Finite.RecentredTransform.cgtransform P R hL N) :=
    (Cvs.Finite.RecentredTransform.differentiable_cgtransform P R hL N).continuous
  have hclosed : IsClosed {z : ℂ |
      ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖
          * ‖w₀ ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
        ≤ ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖
          * ‖z ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
          * exp (‖z ^ 2‖ * ((shiftP (secPolyP L N (ground P R L hL N))).roots.map
              fun r => ‖r‖⁻¹).sum)
          * exp (‖z * L / (2 * π)‖ ^ 2 / N)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub : offAxes ⊆ {z : ℂ |
      ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N z‖
          * ‖w₀ ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
        ≤ ‖Cvs.Finite.RecentredTransform.cgtransform P R hL N w₀‖
          * ‖z ^ 2‖ ^ (secPolyP L N (ground P R L hL N)).natTrailingDegree
          * exp (‖z ^ 2‖ * ((shiftP (secPolyP L N (ground P R L hL N))).roots.map
              fun r => ‖r‖⁻¹).sum)
          * exp (‖z * L / (2 * π)‖ ^ 2 / N)} := fun z hz =>
    Cvs.Limit.RecentredDiagonalBound.norm_cgtransform_le P R hL hN
      (Cvs.Finite.RecentredTransformEven.omega_add_ne_zero hz) (sq_ne_zero_of_offAxes hz)
      (fun j => qf_sub_sq_ne_zero N j hz)
      (Cvs.Finite.RecentredTransformEven.omega_add_ne_zero hwoff) (sq_ne_zero_of_offAxes hwoff)
      (fun j => qf_sub_sq_ne_zero N j hwoff) hw₀
  have hall := closure_minimal hsub hclosed
  rw [Cvs.Upstream.OffAxesDense.dense_offAxes.closure_eq] at hall
  exact hall (Set.mem_univ z)

end Cvs.Limit.RecentredPointwiseBound
