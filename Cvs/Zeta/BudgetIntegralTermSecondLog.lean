import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# The integral term contributes a second `(log 2)√x`
-/

namespace Cvs.Deficit

open MeasureTheory

/-- Powers are integrable away from the origin. -/
theorem integrableOn_rpow (r x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioc 1 x) := by
  refine IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  refine ContinuousOn.rpow_const continuousOn_id ?_
  intro t ht
  exact Or.inl (by have := (Set.mem_Icc.mp ht).1; linarith)

end Cvs.Deficit
