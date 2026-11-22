import Mathlib
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin

/-!
# The symbol's increment grows at most quadratically

    archSymbol t − archSymbol 0 ≤ (2 + t²/8) · levyMass

for every `t`, from `Cvs.Zeta.DigammaLimitDischarged`'s Lévy representation and the pointwise bound
`1 − cos(tu/2) ≤ (2 + t²/8)·min(1, u²)` against a finite Lévy measure.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic

open Cvs.WeilForm.Archimedean.LevyDensity Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- The Lévy measure's total mass against `min(1, u²)`. -/
def levyMass : ℝ := ∫ u in Ioi (0:ℝ), min 1 (u ^ 2) * densityU u

theorem levyMass_nonneg : 0 ≤ levyMass := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  exact mul_nonneg (le_min zero_le_one (sq_nonneg u)) (densityU_pos hu).le

/-- **The symbol's increment is at most quadratic.**  Unconditional, and with no case split
on `|t|`: the Lévy integrand is dominated at every frequency at once. -/
theorem archSymbol_sub_le (t : ℝ) :
    archSymbol t - archSymbol 0 ≤ (2 + t ^ 2 / 8) * levyMass := by
  have hle : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u)
      ≤ ∫ u in Ioi (0:ℝ), (2 + t ^ 2 / 8) * (min 1 (u ^ 2) * densityU u) := by
    refine setIntegral_mono_on (Cvs.WeilForm.Archimedean.ArchTrigonometricData.integrableOn_levyIntegrand t)
      (Cvs.WeilForm.Archimedean.LevyMeasure.integrableOn_min_mul_densityU.const_mul _) measurableSet_Ioi ?_
    intro u hu
    have hd : 0 ≤ densityU u := (densityU_pos hu).le
    unfold Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand
    calc (1 - Real.cos (t / 2 * u)) * densityU u
        ≤ ((2 + t ^ 2 / 8) * min 1 (u ^ 2)) * densityU u :=
          mul_le_mul_of_nonneg_right (Cvs.WeilForm.Archimedean.ArchTrigonometricData.one_sub_cos_le t u) hd
      _ = (2 + t ^ 2 / 8) * (min 1 (u ^ 2) * densityU u) := by ring
  rw [Cvs.WeilForm.Archimedean.ArchTrigonometricData.integral_levyIntegrand t, integral_const_mul] at hle
  exact hle

/-- **And it is nonnegative**, so the increment is squeezed between `0` and a quadratic. -/
theorem archSymbol_sub_nonneg (t : ℝ) : 0 ≤ archSymbol t - archSymbol 0 := by
  have h := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t
  linarith

end Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
