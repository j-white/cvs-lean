import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityEvenBranch
import Cvs.Zeta.ConvexityScaleComparison

/-!
# The edge becomes constant, on the even branch
-/

open Complex

namespace Cvs.ArchScore

/-- **The edge becomes constant, on the even branch.** with `ConvexityEvenBranch` in place of and `ConvexityScaleComparison` in place
of — the structure is unchanged, which is the point. -/
theorem edge_const_even {f : ℂ → ℂ} {c K a b' Ca β : ℝ}
    (hK : (β + c) ^ 2 < K) (ha : 0 ≤ a) (hCa : 0 ≤ Ca)
    {s : ℂ} (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β) (him : 1 ≤ |s.im|)
    (hedge : ‖f s‖ ≤ Ca * (1 + |s.im|) ^ a) :
    ‖f s‖ * Real.exp (-a * (Cvs.ArchScore.evenLog c K s).re
        + b' * s.im * (Cvs.ArchScore.evenLog c K s).im)
      ≤ Ca * 2 ^ a * Real.exp (|b'| * (Real.pi * (β + c) / 2)) := by
  set w : ℂ := (K : ℂ) - (s + (c : ℂ)) ^ 2 with hw
  have hwre : 0 < w.re := Cvs.ArchScore.arg_re_pos hK hc hβ
  have hwpos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le hwre (Complex.re_le_norm w)
  -- split the exponential
  rw [Real.exp_add]
  -- the power factor
  have hre : (Cvs.ArchScore.evenLog c K s).re = Real.log ‖w‖ / 2 := Cvs.ArchScore.evenLog_re c K s
  have hpowerid : Real.exp (-a * (Cvs.ArchScore.evenLog c K s).re) = ‖w‖ ^ (-(a / 2)) := by
    rw [hre, Real.rpow_def_of_pos hwpos]
    congr 1
    ring
  have hpow : ‖f s‖ * ‖w‖ ^ (-(a / 2)) ≤ Ca * 2 ^ a := by
    have hr := Cvs.ArchScore.rpow_ratio_even hK ha hc hβ him
    have hinv : ‖w‖ ^ (-(a / 2)) = (‖w‖ ^ (a / 2))⁻¹ := by
      rw [Real.rpow_neg hwpos.le]
    rw [hinv]
    have hpa : (0 : ℝ) < ‖w‖ ^ (a / 2) := Real.rpow_pos_of_pos hwpos _
    rw [mul_inv_le_iff₀ hpa]
    calc ‖f s‖ ≤ Ca * (1 + |s.im|) ^ a := hedge
      _ ≤ Ca * (2 ^ a * ‖w‖ ^ (a / 2)) := mul_le_mul_of_nonneg_left hr hCa
      _ = Ca * 2 ^ a * ‖w‖ ^ (a / 2) := by ring
  -- the rotation factor
  have hrot : b' * s.im * (Cvs.ArchScore.evenLog c K s).im ≤ |b'| * (Real.pi * (β + c) / 2) := by
    have hb := Cvs.ArchScore.abs_im_mul_im_evenLog_le hK hc hβ
    have hassoc : b' * s.im * (Cvs.ArchScore.evenLog c K s).im
        = b' * (s.im * (Cvs.ArchScore.evenLog c K s).im) := by ring
    rw [hassoc]
    calc b' * (s.im * (Cvs.ArchScore.evenLog c K s).im)
        ≤ |b' * (s.im * (Cvs.ArchScore.evenLog c K s).im)| := le_abs_self _
      _ = |b'| * |s.im * (Cvs.ArchScore.evenLog c K s).im| := by rw [abs_mul]
      _ ≤ |b'| * (Real.pi * (β + c) / 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  rw [hpowerid]
  calc ‖f s‖ * (‖w‖ ^ (-(a / 2)) * Real.exp (b' * s.im * (Cvs.ArchScore.evenLog c K s).im))
      = (‖f s‖ * ‖w‖ ^ (-(a / 2)))
        * Real.exp (b' * s.im * (Cvs.ArchScore.evenLog c K s).im) := by ring
    _ ≤ (Ca * 2 ^ a) * Real.exp (|b'| * (Real.pi * (β + c) / 2)) := by
        refine mul_le_mul hpow (Real.exp_le_exp.mpr hrot) (Real.exp_pos _).le ?_
        positivity

end Cvs.ArchScore
