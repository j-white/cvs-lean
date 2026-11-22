import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowCOneProfileTame

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even first-cell energy is a Gram form of the rung cell profiles

With `r_j = √(1/(2x)) (G_{e_j} + √x E_{G_{e_j}})` in `L²(1/2, 1]`, `cellEnergy x b = bᵀ(gram r)b`. Hence
`gram r ≻ 0` iff the `r_j` are independent iff `cellEnergy` is definite, and then `σ'_t = ((gram r)⁻¹)_tt` is the
least cell energy on `b_t = 1`, it is `CoefficientFloorLinearBound`'s optimal unit-coefficient floor, and the sharp constant in
`b_t² ≤ C · cellEnergy x b` is `1/σ'_t` (T1); at the top rung `t = x − 1` this is CR-E.
-/

noncomputable section

open Real Set MeasureTheory Matrix

namespace Cvs.Prolate.Gram.EvenFirstCellEnergyGram

open Cvs.Xi.EImageWindowPoisson (eimage)

/-- The cell space `L²((1/2, 1])`. -/
abbrev L2c : Type := Lp ℝ 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1))

/-- The cell profile of rung `j`: `√(1/(2x)) (G_{e_j} + E_{G_{e_j}}/√(1/x))`. -/
def rungCell (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) (u : ℝ) : ℝ :=
  √(1 / (x : ℝ) / 2) * (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) u
    + eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) u / √(1 / (x : ℝ)))

/-- The scaled cell profile of a spine class is the coefficient combination of the rung cell profiles. -/
theorem cellProfile_eq_sum (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (u : ℝ) :
    √(1 / (x : ℝ) / 2) * (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b u
      + eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) u / √(1 / (x : ℝ)))
      = ∑ j, b j * rungCell x j u := by
  rw [Cvs.Approximant.SpineCoefficientMatrix.spineG_eq_sum, Cvs.Xi.EImageWindowPoisson.eimage_sum]
  simp only [rungCell, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Each rung cell profile is square integrable on the cell. -/
theorem memLp_rungCell (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    MemLp (rungCell x j) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hx : 0 < x := by
    have := (Finset.mem_filter.mp j.2).1
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  have ha : (0 : ℝ) < 1 / x := by positivity
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j (1 : ℝ))
  have hGc : ContinuousOn G (Icc (-1) 1) := Cvs.L2a.SpineProfileWindowNormPos.continuousOn_spineG _ _
  have hGc0 : ContinuousOn G (Icc 0 1) := hGc.mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc0
  have hMa : ∀ u ∈ Icc (0 : ℝ) 1, |G u| ≤ M := fun u hu => by simpa [Real.norm_eq_abs] using hM u hu
  have hsub : Ioc (1 / 2 : ℝ) 1 ⊆ Icc 0 1 := fun u hu => ⟨by linarith [hu.1], hu.2⟩
  have hmeas : AEStronglyMeasurable (rungCell x j) (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable G (volume.restrict (Ioc (1 / 2 : ℝ) 1)) :=
      (hGc0.mono hsub).aestronglyMeasurable measurableSet_Ioc
    have h2 : AEStronglyMeasurable (fun u => eimage (1 / x) G u / √(1 / (x : ℝ)))
        (volume.restrict (Ioc (1 / 2 : ℝ) 1)) :=
      ((Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc0).div_const _).aestronglyMeasurable
    exact (h1.add h2).const_mul _
  refine MemLp.of_bound hmeas (√(1 / (x : ℝ) / 2) * (M + M / √(1 / (x : ℝ)))) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with u hu
  have hu0 : 0 < u := by linarith [hu.1]
  rw [rungCell, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (hMa u (hsub hu)) ?_))
    (sqrt_nonneg _)
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (Cvs.Xi.WindowCOneProfileTame.abs_eimage_le ha hMa hu0) (sqrt_nonneg _)

/-- The rung vector `r_j ∈ L²((1/2, 1])`. -/
def rungVec (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : L2c := (memLp_rungCell x j).toLp (rungCell x j)

section Floor

variable {x : ℕ} (hM : (gram ℝ (rungVec x)).PosDef)
include hM

end Floor

/-! ### The top rung -/

end Cvs.Prolate.Gram.EvenFirstCellEnergyGram
