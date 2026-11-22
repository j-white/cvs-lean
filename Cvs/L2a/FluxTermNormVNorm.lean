import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An `f u` term by the norm of `f` and the `V`-norm of `u`, with no square root

For `P > 0` on `[L, R]` and `λ > 0`, `|∫ α f u| ≤ (λ/2)∫ α² P f² + (1/2λ)∫ u²/P`, pointwise from
`2|xy| ≤ λx² + y²/λ` on `x = α√P f`, `y = u/√P` without forming the roots; with `α² P ≤ C` on `[L, R]` this is
`(λC/2)∫ f² + (1/2λ)∫ u²/P`: the cost of an `f u` term of the hierarchy in terms of the combination norm (Cvs.L2a.HierarchyLeafMasses)
and the `V`-norm (Cvs.L2a.DilatedVNormMasses), `P = p q̄`.
-/

namespace Cvs.L2a.FluxTermNormVNorm

open Real Set intervalIntegral

/-- **Pointwise**: `−λ P α² f²/2 − u²/(2λP) ≤ α f u ≤ λ P α² f²/2 + u²/(2λP)` for `P, λ > 0`. -/
theorem abs_mul_le_of_pos {al f u P lam : ℝ} (hP : 0 < P) (hl : 0 < lam) :
    |al * (f * u)| ≤ lam / 2 * (al ^ 2 * P * f ^ 2) + 1 / (2 * lam) * (u ^ 2 / P) := by
  have h0 : 0 ≤ (lam * P * (al * f) + u) ^ 2 / (lam * P) := div_nonneg (sq_nonneg _) (by positivity)
  have h1 : 0 ≤ (lam * P * (al * f) - u) ^ 2 / (lam * P) := div_nonneg (sq_nonneg _) (by positivity)
  have e0 : (lam * P * (al * f) + u) ^ 2 / (lam * P)
      = 2 * (lam / 2 * (al ^ 2 * P * f ^ 2) + 1 / (2 * lam) * (u ^ 2 / P)) + 2 * (al * (f * u)) := by
    field_simp; ring
  have e1 : (lam * P * (al * f) - u) ^ 2 / (lam * P)
      = 2 * (lam / 2 * (al ^ 2 * P * f ^ 2) + 1 / (2 * lam) * (u ^ 2 / P)) - 2 * (al * (f * u)) := by
    field_simp; ring
  rw [abs_le]; constructor <;> linarith

/-- **An `f u` term with no square root**: `|∫ α f u| ≤ (λ/2)∫ α² P f² + (1/2λ)∫ u²/P` for `P > 0` on `[L, R]`. -/
theorem fu_term_le_prod {al f u P : ℝ → ℝ} {L R lam : ℝ} (hLR : L ≤ R) (hl : 0 < lam)
    (hP : ∀ θ ∈ Icc L R, 0 < P θ) (hal : ContinuousOn al (Icc L R)) (hf : ContinuousOn f (Icc L R))
    (hu : ContinuousOn u (Icc L R)) (hPc : ContinuousOn P (Icc L R)) :
    |∫ θ in L..R, al θ * (f θ * u θ)|
      ≤ lam / 2 * (∫ θ in L..R, al θ ^ 2 * P θ * f θ ^ 2) + 1 / (2 * lam) * ∫ θ in L..R, u θ ^ 2 / P θ := by
  have hI : IntervalIntegrable (fun θ => al θ * (f θ * u θ)) MeasureTheory.volume L R :=
    (hal.mul (hf.mul hu)).intervalIntegrable_of_Icc hLR
  have hI1 : IntervalIntegrable (fun θ => al θ ^ 2 * P θ * f θ ^ 2) MeasureTheory.volume L R :=
    (((hal.pow 2).mul hPc).mul (hf.pow 2)).intervalIntegrable_of_Icc hLR
  have hI2 : IntervalIntegrable (fun θ => u θ ^ 2 / P θ) MeasureTheory.volume L R :=
    ((hu.pow 2).div hPc fun θ hθ => (hP θ hθ).ne').intervalIntegrable_of_Icc hLR
  calc |∫ θ in L..R, al θ * (f θ * u θ)| ≤ ∫ θ in L..R, |al θ * (f θ * u θ)| := abs_integral_le_integral_abs hLR
    _ ≤ ∫ θ in L..R, (lam / 2 * (al θ ^ 2 * P θ * f θ ^ 2) + 1 / (2 * lam) * (u θ ^ 2 / P θ)) :=
        integral_mono_on hLR hI.abs ((hI1.const_mul _).add (hI2.const_mul _))
          fun θ hθ => abs_mul_le_of_pos (hP θ hθ) hl
    _ = _ := by rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul]

/-- **With a sup bound on the weight**: `α² P ≤ C` on `[L, R]` gives `|∫ α f u| ≤ (λC/2)∫ f² + (1/2λ)∫ u²/P`. -/
theorem fu_term_le_sup {al f u P : ℝ → ℝ} {L R lam C : ℝ} (hLR : L ≤ R) (hl : 0 < lam)
    (hP : ∀ θ ∈ Icc L R, 0 < P θ) (hC : ∀ θ ∈ Icc L R, al θ ^ 2 * P θ ≤ C)
    (hal : ContinuousOn al (Icc L R)) (hf : ContinuousOn f (Icc L R))
    (hu : ContinuousOn u (Icc L R)) (hPc : ContinuousOn P (Icc L R)) :
    |∫ θ in L..R, al θ * (f θ * u θ)|
      ≤ lam * C / 2 * (∫ θ in L..R, f θ ^ 2) + 1 / (2 * lam) * ∫ θ in L..R, u θ ^ 2 / P θ := by
  have h := fu_term_le_prod hLR hl hP hal hf hu hPc
  have hI1 : IntervalIntegrable (fun θ => al θ ^ 2 * P θ * f θ ^ 2) MeasureTheory.volume L R :=
    (((hal.pow 2).mul hPc).mul (hf.pow 2)).intervalIntegrable_of_Icc hLR
  have hIf : IntervalIntegrable (fun θ => f θ ^ 2) MeasureTheory.volume L R := (hf.pow 2).intervalIntegrable_of_Icc hLR
  have h2 : ∫ θ in L..R, al θ ^ 2 * P θ * f θ ^ 2 ≤ C * ∫ θ in L..R, f θ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono_on hLR hI1 (hIf.const_mul _) fun θ hθ =>
      mul_le_mul_of_nonneg_right (hC θ hθ) (sq_nonneg _)
  calc |∫ θ in L..R, al θ * (f θ * u θ)|
      ≤ lam / 2 * (∫ θ in L..R, al θ ^ 2 * P θ * f θ ^ 2) + 1 / (2 * lam) * ∫ θ in L..R, u θ ^ 2 / P θ := h
    _ ≤ lam / 2 * (C * ∫ θ in L..R, f θ ^ 2) + 1 / (2 * lam) * ∫ θ in L..R, u θ ^ 2 / P θ := by
        gcongr
    _ = _ := by ring

end Cvs.L2a.FluxTermNormVNorm
