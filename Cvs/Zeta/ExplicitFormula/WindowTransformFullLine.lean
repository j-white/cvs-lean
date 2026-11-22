import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# The window transform as a full-line integral
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- The test cut off at the endpoints — the compactly supported object the
transform actually integrates. -/
noncomputable def truncate (L : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  Set.indicator (Set.Ioc 0 L) f

theorem truncate_of_mem {L : ℝ} {f : ℝ → ℂ} {s : ℝ} (hs : s ∈ Set.Ioc 0 L) :
    truncate L f s = f s := Set.indicator_of_mem hs f

theorem truncate_of_not_mem {L : ℝ} {f : ℝ → ℂ} {s : ℝ} (hs : s ∉ Set.Ioc 0 L) :
    truncate L f s = 0 := Set.indicator_of_notMem hs f

/-- **Compact support** -- the property the whole downstream chain needs. -/
theorem support_truncate (L : ℝ) (f : ℝ → ℂ) :
    Function.support (truncate L f) ⊆ Set.Ioc 0 L := by
  intro s hs
  by_contra hns
  exact hs (truncate_of_not_mem hns)

/-- **The transform is a full-line integral of a compactly supported function.** -/
theorem windowTransform_eq_integral {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℂ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L f ξ
      = ∫ s : ℝ, Complex.exp (-((s : ℂ) * ξ) * I) * truncate L f s := by
  have hpt : ∀ s : ℝ,
      Complex.exp (-((s : ℂ) * ξ) * I) * truncate L f s
        = Set.indicator (Set.Ioc 0 L)
            (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * f s) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
    · rw [truncate_of_mem hs, Set.indicator_of_mem hs]
    · rw [truncate_of_not_mem hs, Set.indicator_of_notMem hs, mul_zero]
  rw [Cvs.Detection.windowTransform, intervalIntegral.integral_of_le hL]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]

/-- The cut-off test is integrable, for continuous `f`.  No sign condition on
`L` is needed: if `L < 0` the interval is empty. -/
theorem integrable_truncate (L : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (truncate L f) := by
  rw [truncate, MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
  exact (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

end Cvs.Detection
