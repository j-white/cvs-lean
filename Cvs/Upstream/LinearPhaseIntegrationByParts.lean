import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One integration by parts against a linear phase, and the product of two modulated functions

`|∫_p^q a(x)cos(lx + φ)| ≤ (|a(p)| + |a(q)| + ∫_p^q |a′|)/|l|` for every `φ`, so the sine at `φ − π/2`; and
`(A cos α + B sin α)(A′ cos β + B′ sin β)` is exactly half the amplitude products at `α − β` plus half at `α + β`, so the
cross term of two modulated functions (an earlier result) is four such integrals at the difference and sum frequencies.
-/

namespace Cvs.Upstream.LinearPhaseIntegrationByParts

open Real Set MeasureTheory intervalIntegral

/-- **Integration by parts against `cos(lx + φ)`.** -/
theorem abs_integral_mul_cos_le {a a' : ℝ → ℝ} {p q l φ : ℝ} (hpq : p ≤ q) (hl : l ≠ 0)
    (ha : ∀ x ∈ uIcc p q, HasDerivAt a (a' x) x) (ha'c : ContinuousOn a' (uIcc p q)) :
    |∫ x in p..q, a x * Real.cos (l * x + φ)|
      ≤ (|a p| + |a q| + ∫ x in p..q, |a' x|) / |l| := by
  have hv : ∀ x ∈ uIcc p q, HasDerivAt (fun x => Real.sin (l * x + φ) / l) (Real.cos (l * x + φ)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => l * x + φ) l x := by
      simpa using ((hasDerivAt_id x).const_mul l).add_const φ
    have h2 := h1.sin.div_const l
    refine h2.congr_deriv ?_
    field_simp
  have hcos : IntervalIntegrable (fun x => Real.cos (l * x + φ)) volume p q :=
    (Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)).intervalIntegrable _ _
  have hibp := integral_mul_deriv_eq_deriv_mul ha hv (ha'c.intervalIntegrable) hcos
  rw [hibp]
  have hl0 : 0 < |l| := abs_pos.mpr hl
  have hsin : ∀ x, |Real.sin (l * x + φ) / l| ≤ 1 / |l| := fun x => by
    rw [abs_div]; exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hl0.le
  have hint : |∫ x in p..q, a' x * (Real.sin (l * x + φ) / l)| ≤ (∫ x in p..q, |a' x|) / |l| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun x => a' x * (Real.sin (l * x + φ) / l)) hpq
    refine h.trans ?_
    rw [div_eq_mul_one_div, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on hpq
    · have hsc : Continuous (fun x => Real.sin (l * x + φ) / l) := by fun_prop
      exact (ha'c.mul hsc.continuousOn).abs.intervalIntegrable
    · exact (ha'c.abs.intervalIntegrable.mul_const _)
    · intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hsin x) (abs_nonneg _)
  have e1 := hsin q
  have e2 := hsin p
  calc |a q * (Real.sin (l * q + φ) / l) - a p * (Real.sin (l * p + φ) / l)
        - ∫ x in p..q, a' x * (Real.sin (l * x + φ) / l)|
      ≤ |a q| * (1 / |l|) + |a p| * (1 / |l|) + (∫ x in p..q, |a' x|) / |l| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) hint)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
    _ = (|a p| + |a q| + ∫ x in p..q, |a' x|) / |l| := by field_simp; ring

end Cvs.Upstream.LinearPhaseIntegrationByParts
