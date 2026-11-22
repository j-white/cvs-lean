import Mathlib
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# A nonnegative test has a nonnegative prime side, and that is the trade
-/

namespace Cvs.Detection

open Complex MeasureTheory ArithmeticFunction FourierTransform
open scoped Real

/-- The real autocorrelation. -/
noncomputable def autocorrR (L : ℝ) (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Set.indicator (Set.Ioc 0 L) f (s - v)

theorem truncate_ofReal (L : ℝ) (f : ℝ → ℝ) (s : ℝ) :
    Cvs.Detection.truncate L (fun t => ((f t : ℝ) : ℂ)) s
      = ((Set.indicator (Set.Ioc 0 L) f s : ℝ) : ℂ) := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
  · rw [Cvs.Detection.truncate_of_mem hs, Set.indicator_of_mem hs]
  · rw [Cvs.Detection.truncate_of_not_mem hs, Set.indicator_of_notMem hs]
    simp

theorem autocorr_ofReal (L : ℝ) (f : ℝ → ℝ) (v : ℝ) :
    Cvs.Detection.autocorr L (fun t => ((f t : ℝ) : ℂ)) v = ((autocorrR L f v : ℝ) : ℂ) := by
  rw [Cvs.Detection.autocorr, autocorrR, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Cvs.Detection.truncate L (fun t => ((f t : ℝ) : ℂ)) s
      * Cvs.Detection.truncate L (fun t => ((f t : ℝ) : ℂ)) (s - v)
    = ((Set.indicator (Set.Ioc 0 L) f s
        * Set.indicator (Set.Ioc 0 L) f (s - v) : ℝ) : ℂ)
  rw [truncate_ofReal, truncate_ofReal]
  push_cast
  ring

end Cvs.Detection
