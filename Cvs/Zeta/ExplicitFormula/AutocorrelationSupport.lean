import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The autocorrelation vanishes outside `(−L, L)`

`WindowTransformFullLine` made the transform a full-line integral of `truncate L f`, a compactly supported
function.
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- The autocorrelation of the cut-off test. -/
noncomputable def autocorr (L : ℝ) (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ s : ℝ, Cvs.Detection.truncate L f s * Cvs.Detection.truncate L f (s - v)

/-- The two factors cannot both be nonzero once `|v| ≥ L`. -/
theorem integrand_eq_zero {L : ℝ} (f : ℝ → ℂ) {v : ℝ} (hv : L ≤ |v|) (s : ℝ) :
    Cvs.Detection.truncate L f s * Cvs.Detection.truncate L f (s - v) = 0 := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
  · by_cases hsv : s - v ∈ Set.Ioc (0 : ℝ) L
    · exfalso
      rw [Set.mem_Ioc] at hs hsv
      rcases abs_cases v with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hv; linarith [hs.2, hsv.1]
      · rw [he] at hv; linarith [hs.1, hsv.2]
    · rw [Cvs.Detection.truncate_of_not_mem hsv, mul_zero]
  · rw [Cvs.Detection.truncate_of_not_mem hs, zero_mul]

/-- **The autocorrelation vanishes outside `(−L, L)`.** -/
theorem autocorr_eq_zero_of_abs_ge {L : ℝ} (f : ℝ → ℂ) {v : ℝ} (hv : L ≤ |v|) :
    autocorr L f v = 0 := by
  rw [autocorr]
  simp_rw [integrand_eq_zero f hv]
  exact integral_zero ℝ ℂ

theorem support_autocorr (L : ℝ) (f : ℝ → ℂ) :
    Function.support (autocorr L f) ⊆ Set.Ioo (-L) L := by
  intro v hv
  by_contra hns
  apply hv
  refine autocorr_eq_zero_of_abs_ge f ?_
  rw [Set.mem_Ioo] at hns
  rw [not_and_or] at hns
  rcases hns with h | h
  · rw [not_lt] at h
    exact le_abs.mpr (Or.inr (by linarith))
  · rw [not_lt] at h
    exact le_abs.mpr (Or.inl h)

end Cvs.Detection
