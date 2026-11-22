import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The Lévy density is decreasing

    0 < u ≤ v  ⟹  densityU v ≤ densityU u

its numerator falls and its denominator rises, so a dilation that contracts the displacement
can only raise the density, by a factor the comparison controls.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.Archimedean.LevyDensityDecreasing

/-- **The Lévy density is decreasing on the positive axis.** -/
theorem densityU_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU v ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hdu : 0 < 1 - Real.exp (-u) := by
    have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hdv : 0 < 1 - Real.exp (-v) := by
    have : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU, Cvs.WeilForm.Archimedean.LevyDensity.densityU,
    div_le_div_iff₀ hdv hdu]
  have hnum : Real.exp (-(v / 4)) ≤ Real.exp (-(u / 4)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-u) ≤ 1 - Real.exp (-v) := by
    have : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    linarith
  nlinarith [Real.exp_pos (-(v / 4)), Real.exp_pos (-(u / 4)), hnum, hden, hdu, hdv]

/-- **A contracted displacement raises the density by at most the halving comparison.** -/
theorem densityU_dilate_le {a u : ℝ} (hu : 0 < u) (ha : 1 / 2 ≤ a) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU (a * u) ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (u / 2) := by
  refine densityU_antitone (by positivity) ?_
  nlinarith [hu, ha]

end Cvs.WeilForm.Archimedean.LevyDensityDecreasing
