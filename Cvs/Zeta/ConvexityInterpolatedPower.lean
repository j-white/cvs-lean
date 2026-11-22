import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEvenBranch
import Cvs.Zeta.ConvexityPhragmenLindelof
import Cvs.Zeta.ConvexityScaleComparison

/-!
# Undoing the damping, and the interpolated power bound

The convexity argument's last general step.
-/

open Complex

namespace Cvs.ArchScore

/-- **The damping scale is at most quadratic in the height.**  The companion to `ConvexityScaleComparison`'s lower
bound, needed when the damping is undone. -/
theorem norm_le_sq {c K β : ℝ} (hK : 0 ≤ K) (hβc : 1 ≤ β + c) {s : ℂ}
    (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) :
    ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ ≤ (K + (β + c) ^ 2) * (1 + |s.im|) ^ 2 := by
  have hsc : ‖s + (c : ℂ)‖ ≤ (β + c) * (1 + |s.im|) := by
    have h1 : ‖s + (c : ℂ)‖ ≤ |(s + (c : ℂ)).re| + |(s + (c : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    have hre : |(s + (c : ℂ)).re| ≤ β + c := by
      have hval : (s + (c : ℂ)).re = s.re + c := by simp
      rw [hval, abs_of_nonneg hc]; linarith
    have him : |(s + (c : ℂ)).im| = |s.im| := by simp
    rw [him] at h1
    nlinarith [abs_nonneg s.im, hβc]
  have hsq : ‖(s + (c : ℂ)) ^ 2‖ ≤ (β + c) ^ 2 * (1 + |s.im|) ^ 2 := by
    rw [norm_pow]
    have hnn : (0:ℝ) ≤ ‖s + (c : ℂ)‖ := norm_nonneg _
    nlinarith [hsc, hnn, abs_nonneg s.im]
  have hone : (1:ℝ) ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
  calc ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ ≤ ‖(K : ℂ)‖ + ‖(s + (c : ℂ)) ^ 2‖ := norm_sub_le _ _
    _ ≤ K + (β + c) ^ 2 * (1 + |s.im|) ^ 2 := by
        have : ‖(K : ℂ)‖ = K := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
        linarith [hsq, this.le, this.ge]
    _ ≤ (K + (β + c) ^ 2) * (1 + |s.im|) ^ 2 := by nlinarith [hone, hK]

/-- **Undoing the damping into an interpolated power bound.** -/
theorem norm_le_rpow_of_aux_le {f : ℂ → ℂ} {c K a' b' C β : ℝ}
    (hK : (β + c) ^ 2 < K) (hKnn : 0 ≤ K) (hβc : 1 ≤ β + c)
    {s : ℂ} (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) (him : 1 ≤ |s.im|)
    (hp : 0 ≤ a' + b' * s.re) (hC : 0 ≤ C)
    (h : ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' s‖ ≤ C) :
    ‖f s‖ ≤ C * Real.exp (|b'| * (Real.pi * (β + c) / 2))
        * ((K + (β + c) ^ 2) ^ ((a' + b' * s.re) / 2)
          * (1 + |s.im|) ^ (a' + b' * s.re)) := by
  set w : ℂ := (K : ℂ) - (s + (c : ℂ)) ^ 2 with hw
  have hwre : 0 < w.re := Cvs.ArchScore.arg_re_pos hK hc hβ
  have hwpos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le hwre (Complex.re_le_norm w)
  have hundo := Cvs.ArchScore.norm_le_of_norm_aux_le h
  have hre : (Cvs.ArchScore.evenLog c K s).re = Real.log ‖w‖ / 2 := Cvs.ArchScore.evenLog_re c K s
  -- the power factor becomes `‖w‖ ^ ((a'+b'σ)/2)`
  have hpower : Real.exp ((a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re)
      = ‖w‖ ^ ((a' + b' * s.re) / 2) := by
    rw [hre, Real.rpow_def_of_pos hwpos]
    congr 1; ring
  -- the rotation factor is bounded
  have hrot : -(b' * s.im * (Cvs.ArchScore.evenLog c K s).im)
      ≤ |b'| * (Real.pi * (β + c) / 2) := by
    have hb := Cvs.ArchScore.abs_im_mul_im_evenLog_le hK hc hβ
    have hassoc : b' * s.im * (Cvs.ArchScore.evenLog c K s).im
        = b' * (s.im * (Cvs.ArchScore.evenLog c K s).im) := by ring
    rw [hassoc]
    calc -(b' * (s.im * (Cvs.ArchScore.evenLog c K s).im))
        ≤ |b' * (s.im * (Cvs.ArchScore.evenLog c K s).im)| := neg_le_abs _
      _ = |b'| * |s.im * (Cvs.ArchScore.evenLog c K s).im| := by rw [abs_mul]
      _ ≤ |b'| * (Real.pi * (β + c) / 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  -- the scale bound
  have hscale : ‖w‖ ^ ((a' + b' * s.re) / 2)
      ≤ (K + (β + c) ^ 2) ^ ((a' + b' * s.re) / 2) * (1 + |s.im|) ^ (a' + b' * s.re) := by
    have hup := norm_le_sq (c := c) (K := K) (β := β) hKnn hβc hc hβ
    have hmono : ‖w‖ ^ ((a' + b' * s.re) / 2)
        ≤ ((K + (β + c) ^ 2) * (1 + |s.im|) ^ 2) ^ ((a' + b' * s.re) / 2) :=
      Real.rpow_le_rpow hwpos.le hup (by linarith)
    refine le_trans hmono (le_of_eq ?_)
    rw [Real.mul_rpow (by nlinarith [sq_nonneg (β+c)]) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (1 + |s.im|) 2, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast; ring
  rw [Real.exp_sub, hpower] at hundo
  have hexpr : (Real.exp (b' * s.im * (Cvs.ArchScore.evenLog c K s).im))⁻¹
      ≤ Real.exp (|b'| * (Real.pi * (β + c) / 2)) := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr hrot
  calc ‖f s‖ ≤ C * (‖w‖ ^ ((a' + b' * s.re) / 2)
        / Real.exp (b' * s.im * (Cvs.ArchScore.evenLog c K s).im)) := hundo
    _ = C * (‖w‖ ^ ((a' + b' * s.re) / 2)
        * (Real.exp (b' * s.im * (Cvs.ArchScore.evenLog c K s).im))⁻¹) := by
        rw [div_eq_mul_inv]
    _ ≤ C * (((K + (β + c) ^ 2) ^ ((a' + b' * s.re) / 2) * (1 + |s.im|) ^ (a' + b' * s.re))
        * Real.exp (|b'| * (Real.pi * (β + c) / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hscale hexpr (by positivity) (by positivity)) hC
    _ = C * Real.exp (|b'| * (Real.pi * (β + c) / 2))
        * ((K + (β + c) ^ 2) ^ ((a' + b' * s.re) / 2)
          * (1 + |s.im|) ^ (a' + b' * s.re)) := by ring

end Cvs.ArchScore
