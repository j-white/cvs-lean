import Mathlib
import Cvs.Limit.OffAxesLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A bound demanded off the axes is a bound demanded on the whole ball

The points with both coordinates non-zero are dense, being the intersection of two open dense
coordinate halves, so a continuous function bounded there is bounded on the closure, and a ball is
the closure of its open part.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Metric Set Filter

namespace Cvs.Upstream.OffAxesDense

/-- **The points with non-zero real part are dense.** -/
theorem dense_re_ne_zero : Dense {z : ℂ | z.re ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  by_cases hx : x.re = 0
  · refine ⟨x + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · have hd : dist (x + ((r / 2 : ℝ) : ℂ)) x = r / 2 := by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      rw [Metric.mem_ball, hd]
      linarith
    · show (x + ((r / 2 : ℝ) : ℂ)).re ≠ 0
      have hre : (x + ((r / 2 : ℝ) : ℂ)).re = r / 2 := by
        rw [Complex.add_re, Complex.ofReal_re, hx, zero_add]
      rw [hre]
      exact ne_of_gt (by linarith)
  · exact ⟨x, Metric.mem_ball_self hr, hx⟩

/-- **The points with non-zero imaginary part are dense.** -/
theorem dense_im_ne_zero : Dense {z : ℂ | z.im ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  by_cases hx : x.im = 0
  · refine ⟨x + ((r / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · have hd : dist (x + ((r / 2 : ℝ) : ℂ) * Complex.I) x = r / 2 := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [Metric.mem_ball, hd]
      linarith
    · show (x + ((r / 2 : ℝ) : ℂ) * Complex.I).im ≠ 0
      have him : (x + ((r / 2 : ℝ) : ℂ) * Complex.I).im = r / 2 := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hx]
      rw [him]
      exact ne_of_gt (by linarith)
  · exact ⟨x, Metric.mem_ball_self hr, hx⟩

/-- **The points off both coordinate axes are dense in the plane.** -/
theorem dense_offAxes : Dense Cvs.Limit.OffAxesLimit.offAxes := by
  have hset : Cvs.Limit.OffAxesLimit.offAxes = {z : ℂ | z.re ≠ 0} ∩ {z : ℂ | z.im ≠ 0} :=
    Set.ext fun _ => Iff.rfl
  rw [hset]
  exact dense_re_ne_zero.inter_of_isOpen_left dense_im_ne_zero
    (isOpen_compl_singleton.preimage Complex.continuous_re)

end Cvs.Upstream.OffAxesDense
