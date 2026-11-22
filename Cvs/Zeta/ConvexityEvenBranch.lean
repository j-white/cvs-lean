import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The even branch device: the half-strip obstruction was removable
-/

open Complex

namespace Cvs.ArchScore

/-- The **even** branch device: `log(K - (s+c)²)/2`.  Its argument is even in the height, so it
works on the whole strip rather than a half-strip. -/
noncomputable def evenLog (c K : ℝ) (s : ℂ) : ℂ :=
  Complex.log ((K : ℂ) - (s + (c : ℂ)) ^ 2) / 2

theorem sq_re (c : ℝ) (s : ℂ) :
    ((s + (c : ℂ)) ^ 2).re = (s.re + c) ^ 2 - s.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

theorem sq_im (c : ℝ) (s : ℂ) :
    ((s + (c : ℂ)) ^ 2).im = 2 * (s.re + c) * s.im := by
  simp [pow_two, Complex.mul_im]; ring

theorem arg_re (c K : ℝ) (s : ℂ) :
    ((K : ℂ) - (s + (c : ℂ)) ^ 2).re = K - (s.re + c) ^ 2 + s.im ^ 2 := by
  simp [sq_re]; ring

theorem arg_im (c K : ℝ) (s : ℂ) :
    ((K : ℂ) - (s + (c : ℂ)) ^ 2).im = -(2 * (s.re + c) * s.im) := by
  simp [sq_im]

/-- **The real part is strictly positive on the strip** — so the point never approaches the
branch cut, from either side. -/
theorem arg_re_pos {c K β : ℝ} {s : ℂ} (hK : (β + c) ^ 2 < K)
    (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) :
    0 < ((K : ℂ) - (s + (c : ℂ)) ^ 2).re := by
  rw [arg_re]
  have h1 : (s.re + c) ^ 2 ≤ (β + c) ^ 2 := by nlinarith
  nlinarith [sq_nonneg s.im]

/-- **The height times the argument is bounded, on both sides.**  This is what the `/I`
rotation gave only above the axis. -/
theorem abs_im_mul_im_evenLog_le {c K β : ℝ} {s : ℂ} (hK : (β + c) ^ 2 < K)
    (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) :
    |s.im * (evenLog c K s).im| ≤ Real.pi * (β + c) / 2 := by
  set w : ℂ := (K : ℂ) - (s + (c : ℂ)) ^ 2 with hw
  have hwre : 0 < w.re := arg_re_pos hK hc hβ
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hwre; simp at hwre
  have hnorm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
  -- `|arg w| ≤ π/2` since `Re w > 0`
  have harg : |w.arg| ≤ Real.pi / 2 :=
    le_of_lt (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre))
  have hjordan : 2 / Real.pi * |w.arg| ≤ |Real.sin w.arg| := Real.mul_abs_le_abs_sin harg
  have hsin : |Real.sin w.arg| = |w.im| / ‖w‖ := by
    rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg w)]
  -- `‖w‖ ≥ Re w ≥ Im s ^ 2`
  have hge : s.im ^ 2 ≤ ‖w‖ := by
    refine le_trans ?_ (Complex.re_le_norm w)
    rw [hw, arg_re]
    nlinarith [sq_nonneg (s.re + c), hK, sq_nonneg (β + c)]
  have hbound : |w.arg| ≤ Real.pi / 2 * (|w.im| / ‖w‖) := by
    calc |w.arg| = Real.pi / 2 * (2 / Real.pi * |w.arg|) := by field_simp
      _ ≤ Real.pi / 2 * (|w.im| / ‖w‖) := by
          rw [← hsin]; exact mul_le_mul_of_nonneg_left hjordan (by positivity)
  have hwim : |w.im| = 2 * (s.re + c) * |s.im| := by
    rw [hw, arg_im, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (s.re + c))]
  have hevenim : (evenLog c K s).im = w.arg / 2 := by
    rw [evenLog, ← hw]
    simp [Complex.log_im]
  have hstep : |s.im| * |w.arg| ≤ Real.pi * (β + c) := by
    have h1 : |s.im| * |w.arg| ≤ |s.im| * (Real.pi / 2 * (|w.im| / ‖w‖)) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    have hratio : s.im ^ 2 / ‖w‖ ≤ 1 := by
      rw [div_le_one hnorm]; exact hge
    have h2 : |s.im| * (Real.pi / 2 * (|w.im| / ‖w‖))
        = Real.pi * (s.re + c) * (s.im ^ 2 / ‖w‖) := by
      rw [hwim, ← sq_abs s.im]
      field_simp
    rw [h2] at h1
    have h3 : Real.pi * (s.re + c) * (s.im ^ 2 / ‖w‖) ≤ Real.pi * (s.re + c) := by
      have hnn : (0 : ℝ) ≤ Real.pi * (s.re + c) := mul_nonneg Real.pi_pos.le hc
      calc Real.pi * (s.re + c) * (s.im ^ 2 / ‖w‖)
          ≤ Real.pi * (s.re + c) * 1 := mul_le_mul_of_nonneg_left hratio hnn
        _ = Real.pi * (s.re + c) := by ring
    have h4 : Real.pi * (s.re + c) ≤ Real.pi * (β + c) := by
      nlinarith [Real.pi_pos, hβ]
    linarith
  rw [hevenim, abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  linarith [hstep]

end Cvs.ArchScore
