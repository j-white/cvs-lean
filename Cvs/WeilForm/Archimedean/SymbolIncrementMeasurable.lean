import Mathlib
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure

/-!
# The symbol's increment is measurable, and `hWA` holds

    StronglyMeasurable (t ↦ archSymbol t − archSymbol 0)

as a parametric integral of the Lévy integrand, which is jointly measurable; with `an earlier result`'s
decay and `Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic`'s growth this gives the density integrable against the symbol.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Function
open scoped FourierTransform

namespace Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
open Cvs.WeilForm.Archimedean.LevyDensity

/-- The Lévy integrand is jointly measurable. -/
theorem measurable_levyIntegrand :
    Measurable (uncurry fun t u : ℝ => Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u) := by
  unfold Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand
  refine (measurable_const.sub ?_).mul
    (Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.comp measurable_snd)
  exact Real.measurable_cos.comp ((measurable_fst.div_const 2).mul measurable_snd)

/-- **The symbol's increment is measurable.**  This development has no continuity statement for the
digamma real part; `Cvs.WeilForm.Archimedean.ArchTrigonometricData`'s representation makes the increment a parametric integral. -/
theorem stronglyMeasurable_archSymbol_sub :
    StronglyMeasurable fun t : ℝ => archSymbol t - archSymbol 0 := by
  have heq : (fun t : ℝ => archSymbol t - archSymbol 0)
      = fun t : ℝ => ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u := by
    funext t
    exact (Cvs.WeilForm.Archimedean.ArchTrigonometricData.integral_levyIntegrand t).symm
  rw [heq]
  exact MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioi (0:ℝ))) measurable_levyIntegrand.stronglyMeasurable

end Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable
