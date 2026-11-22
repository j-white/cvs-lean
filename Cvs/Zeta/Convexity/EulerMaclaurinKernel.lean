import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Euler–Maclaurin kernel
-/

open Complex MeasureTheory Set

namespace Cvs.ZetaGrowth

/-- The Euler–Maclaurin kernel `{x}·x^{-s-1}`. -/
noncomputable def emKernel (s : ℂ) (x : ℝ) : ℂ :=
  ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

/-- `‖{x}·x^{-s-1}‖ ≤ x^{-σ-1}`: the fractional part is in `[0,1)`. -/
theorem norm_emKernel_le {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖emKernel s x‖ ≤ x ^ (-s.re - 1) := by
  rw [emKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hf : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact le_of_lt (Int.fract_lt_one x)
  have hre : (-s - 1).re = -s.re - 1 := by simp
  rw [hre]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _) hf

theorem aestronglyMeasurable_emKernel (s : ℂ) :
    AEStronglyMeasurable (emKernel s) (volume.restrict (Ioi (1 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) :=
    (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
  have h2 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact (Complex.continuousAt_ofReal_cpow_const x (-s - 1) (Or.inr (ne_of_gt hx0))).continuousWithinAt
  have heq : emKernel s = fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := rfl
  rw [heq]
  exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)

/-- **The kernel is integrable on `[1,∞)` for `σ > 0`.** -/
theorem integrableOn_emKernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (emKernel s) (Ioi (1 : ℝ)) := by
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hdom.mono' (aestronglyMeasurable_emKernel s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_emKernel_le (lt_trans zero_lt_one hx)

end Cvs.ZetaGrowth
