import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The dilation moves onto the Lévy density

    ∫_{u>0} densityU u · d (u/c) du  =  c · ∫_{w>0} densityU (c·w) · d w dw

for `c > 0`, so a dilation of the test function becomes a dilation of the density, where
`Cvs.WeilForm.Archimedean.LevyDensityDecreasing`'s monotonicity dominates it.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set
open scoped Pointwise

namespace Cvs.WeilForm.Archimedean.DilationOntoDensity

/-- Scaling fixes the positive axis. -/
theorem smul_Ioi_zero {c : ℝ} (hc : 0 < c) : c • Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
  rw [LinearOrderedField.smul_Ioi hc, mul_zero]

/-- **The dilation moves onto the density.** -/
theorem integral_dilate_onto_density {c : ℝ} (hc : 0 < c) (d : ℝ → ℝ) :
    (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * d (u / c))
      = c * ∫ w in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU (c * w) * d w := by
  have hsub := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure ℝ))
    (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * d (u / c)) (Set.Ioi (0:ℝ)) hc
  rw [smul_Ioi_zero hc, Module.finrank_self, pow_one] at hsub
  have hrw : ∀ w : ℝ, (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * d (u / c)) (c • w)
      = Cvs.WeilForm.Archimedean.LevyDensity.densityU (c * w) * d w := by
    intro w
    simp only [smul_eq_mul]
    congr 2
    field_simp
  simp only [hrw] at hsub
  rw [smul_eq_mul] at hsub
  field_simp at hsub ⊢
  linarith [hsub]

end Cvs.WeilForm.Archimedean.DilationOntoDensity
