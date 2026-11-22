import Mathlib
import Cvs.WeilForm.WeilFormReflection
import Cvs.Zeta.ExplicitFormula.NonnegTestPrimeSide
import Cvs.Zeta.WeilPositivityStatement

/-!
# The detection autocorrelation is the self-convolution of the truncated test

    autocorrR L f v = selfConvolution (indicator (Ioc 0 L) f) v

and on the half-open window that self-convolution vanishes for `L ≤ |u|`, endpoint included,
because `Ioc 0 L` and its translate by `L` are disjoint.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.AutocorrSelfConvolution

/-- **The two autocorrelations are one object.**  `Detection` reflects the shift; the
self-convolution is even, so the two agree. -/
theorem autocorrR_eq_selfConvolution (L : ℝ) (f : ℝ → ℝ) (v : ℝ) :
    Cvs.Detection.autocorrR L f v
      = selfConvolution (Set.indicator (Set.Ioc 0 L) f) v := by
  rw [Cvs.Detection.autocorrR,
    ← Cvs.WeilForm.WeilFormReflection.selfConvolution_neg (Set.indicator (Set.Ioc 0 L) f) v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [show s + -v = s - v by ring]

/-- **The half-open window's self-convolution vanishes at the endpoint too.**  `Ioc 0 L` and
its translate by `L` are disjoint, so no measure-zero argument is needed. -/
theorem selfConvolution_indicator_eq_zero (L : ℝ) (f : ℝ → ℝ) {u : ℝ} (hu : L ≤ |u|) :
    selfConvolution (Set.indicator (Set.Ioc 0 L) f) u = 0 := by
  have hzero : ∀ s : ℝ, Set.indicator (Set.Ioc 0 L) f s
      * Set.indicator (Set.Ioc 0 L) f (s + u) = 0 := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0:ℝ) L
    · refine mul_eq_zero.mpr (Or.inr ?_)
      refine Set.indicator_of_notMem (fun hsu => ?_) f
      obtain ⟨h1, h2⟩ := hs
      obtain ⟨h3, h4⟩ := hsu
      rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hu <;> linarith
    · exact mul_eq_zero.mpr (Or.inl (Set.indicator_of_notMem hs f))
  unfold selfConvolution
  simp [hzero]

end Cvs.WeilForm.AutocorrSelfConvolution
