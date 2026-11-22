import Mathlib
import Cvs.Zeta.Convexity.CriticalLineHalfExponent
import Cvs.Zeta.ConvexityInterpolatedPower
import Cvs.Zeta.ConvexityZetaEdges

/-!
# The convexity bound in its proper form

‖ζ(σ+it)‖ ≤ C·(1+|t|)^{3/4 - σ/2} for `-1/2 ≤ σ ≤ 3/2`, `|t| ≥ 1`.
-/

open Complex

namespace Cvs.Zeta.Convexity.StripConvexityBound
open Cvs.ZetaGrowth

/-- **The convexity bound in its proper form** , with the interpolated exponent kept. -/
theorem norm_zeta₀_convexity : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 →
    1 ≤ |s.im| → ‖riemannZeta₀ s‖ ≤ C * (1 + |s.im|) ^ (3/4 - s.re/2) := by
  obtain ⟨C, hC⟩ := Cvs.Zeta.Convexity.CriticalLineHalfExponent.aux_bounded
  have hC0 : 0 ≤ C := by
    have := hC (((-1/2 : ℝ) : ℂ)) (by simp) (by simp; norm_num)
    exact le_trans (norm_nonneg _) this
  set E : ℝ := Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) with hE
  have hEp : 0 < E := Real.exp_pos _
  set P : ℝ := ((7 : ℝ) + (3/2 + 1) ^ 2) ^ ((1/2 : ℝ)) with hP
  have hPp : 0 < P := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C * E * P, by positivity, fun s h1 h2 him => ?_⟩
  have ha0 : (0 : ℝ) ≤ 3/4 + (-1/2) * s.re := by linarith
  have hundo := Cvs.ArchScore.norm_le_rpow_of_aux_le (f := riemannZeta₀) (c := 1) (K := 7)
    (a' := 3/4) (b' := -1/2) (C := C) (β := 3/2) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) h2 him ha0 hC0 (hC s h1 h2)
  have heq : (3 : ℝ)/4 + (-1/2) * s.re = 3/4 - s.re/2 := by ring
  rw [heq] at hundo
  refine le_trans hundo ?_
  have hCE : (0 : ℝ) ≤ C * E := mul_nonneg hC0 (le_of_lt hEp)
  have hfac : ((7 : ℝ) + (3/2 + 1) ^ 2) ^ ((3/4 - s.re/2) / 2) ≤ P := by
    rw [hP]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hbase : (0 : ℝ) ≤ (1 + |s.im|) ^ (3/4 - s.re/2) :=
    Real.rpow_nonneg (by linarith [abs_nonneg s.im]) _
  calc C * E * (((7 : ℝ) + (3/2 + 1) ^ 2) ^ ((3/4 - s.re/2) / 2)
          * (1 + |s.im|) ^ (3/4 - s.re/2))
      ≤ C * E * (P * (1 + |s.im|) ^ (3/4 - s.re/2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCE
        exact mul_le_mul_of_nonneg_right hfac hbase
    _ = C * E * P * (1 + |s.im|) ^ (3/4 - s.re/2) := by ring

/-- The same for `ζ`.  The pole term costs `1`, absorbed because the exponent is nonnegative
across the strip so `(1+|t|)^{3/4-σ/2} ≥ 1`. -/
theorem norm_zeta_convexity : ∃ C : ℝ, ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3/4 - s.re/2) := by
  obtain ⟨C, _, hC⟩ := norm_zeta₀_convexity
  refine ⟨C + 1, fun s h1 h2 him => ?_⟩
  have hb : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hone : (1 : ℝ) ≤ (1 + |s.im|) ^ (3/4 - s.re/2) :=
    Real.one_le_rpow hb (by linarith)
  have hz := Cvs.ArchScore.norm_zeta_le_of_zeta₀ him (hC s h1 h2 him)
  have hring : (C + 1) * (1 + |s.im|) ^ (3/4 - s.re/2)
      = C * (1 + |s.im|) ^ (3/4 - s.re/2) + (1 + |s.im|) ^ (3/4 - s.re/2) := by ring
  linarith

end Cvs.Zeta.Convexity.StripConvexityBound
