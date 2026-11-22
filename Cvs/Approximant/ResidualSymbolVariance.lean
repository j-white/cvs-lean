import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.TailRetainedModeCoupling
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.PhysicalCubicCorrectionColumn

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Symbol variance and signed boundary covariance in the actual residual

The residual of a unit vector for a diagonal symbol plus a boundary matrix is its
weighted symbol variance, the boundary energy orthogonal to that vector, and twice
their signed covariance. The full boundary budget retains both signed corrections.
-/

noncomputable section

open Real Matrix Finset

namespace Cvs.Approximant.ResidualSymbolVariance
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- A diagonal symbol acting on a coefficient vector. -/
def diagonalColumn (d v : ι → ℝ) : ι → ℝ := fun i => d i * v i

/-- The mean symbol in the squared coefficient weights of a unit vector. -/
def symbolMean (d v : ι → ℝ) : ℝ := diagonalColumn d v ⬝ᵥ v

/-- The diagonal column with its mean symbol removed. -/
def symbolFluctuation (d v : ι → ℝ) : ι → ℝ :=
  fun i => (d i - symbolMean d v) * v i

/-- Weighted symbol variance, with weights given by squared unit coefficients. -/
def symbolVariance (d v : ι → ℝ) : ℝ :=
  symbolFluctuation d v ⬝ᵥ symbolFluctuation d v

/-- Signed covariance between the fluctuating symbol and a boundary column. -/
def signedCovariance (d v β : ι → ℝ) : ℝ := symbolFluctuation d v ⬝ᵥ β

/-- Centering a column against a unit vector removes exactly its parallel energy. -/
theorem center_sq_unit (u v : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    Cvs.Approximant.ConnesErrorColumn.center u v ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center u v = u ⬝ᵥ u - (u ⬝ᵥ v) ^ 2 := by
  simp only [Cvs.Approximant.ConnesErrorColumn.center, hv, div_one, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]
  ring

/-- The centered diagonal column is the coefficient-weighted fluctuation of its symbol. -/
theorem center_diagonal_unit (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    Cvs.Approximant.ConnesErrorColumn.center (diagonalColumn d v) v = symbolFluctuation d v := by
  funext i
  simp only [Cvs.Approximant.ConnesErrorColumn.center, hv, div_one, diagonalColumn, symbolFluctuation,
    symbolMean, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The weighted symbol fluctuation is orthogonal to its unit coefficient vector. -/
theorem symbolFluctuation_dot (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    symbolFluctuation d v ⬝ᵥ v = 0 := by
  rw [← center_diagonal_unit d v hv]
  exact Cvs.Approximant.ConnesErrorColumn.center_dot _ _

/-- Weighted symbol variance is nonnegative. -/
theorem symbolVariance_nonneg (d v : ι → ℝ) : 0 ≤ symbolVariance d v :=
  Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _

/-- The variance is the sum of squared symbol deviations in coefficient weights. -/
theorem symbolVariance_eq_sum (d v : ι → ℝ) :
    symbolVariance d v = ∑ i, v i ^ 2 * (d i - symbolMean d v) ^ 2 := by
  unfold symbolVariance symbolFluctuation dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The mean symbol is the coefficient-weighted first moment. -/
theorem symbolMean_eq_sum (d v : ι → ℝ) :
    symbolMean d v = ∑ i, v i ^ 2 * d i := by
  unfold symbolMean diagonalColumn dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The weighted symbol variance is its second moment minus the square of its mean. -/
theorem symbolVariance_eq_moments (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    symbolVariance d v = (∑ i, v i ^ 2 * d i ^ 2) - (symbolMean d v) ^ 2 := by
  have hmass : ∑ i, v i ^ 2 = 1 := by simpa only [dotProduct, sq] using hv
  have he : (∑ i, v i ^ 2 * (d i - symbolMean d v) ^ 2) =
      (∑ i, v i ^ 2 * d i ^ 2) - 2 * symbolMean d v * (∑ i, v i ^ 2 * d i)
        + (symbolMean d v) ^ 2 * (∑ i, v i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [symbolVariance_eq_sum, he, ← symbolMean_eq_sum d v, hmass]
  ring

/-- Symbol variance is half the weighted squared pairwise differences. -/
theorem two_symbolVariance_eq_pairwise (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    2 * symbolVariance d v = ∑ i, ∑ j, v i ^ 2 * v j ^ 2 * (d i - d j) ^ 2 := by
  have hmass : ∑ i, v i ^ 2 = 1 := by simpa only [dotProduct, sq] using hv
  have he (i : ι) : (∑ j, v i ^ 2 * v j ^ 2 * (d i - d j) ^ 2) =
      v i ^ 2 * d i ^ 2 * (∑ j, v j ^ 2)
        - 2 * (v i ^ 2 * d i) * (∑ j, v j ^ 2 * d j)
        + v i ^ 2 * (∑ j, v j ^ 2 * d j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl (fun i _ => he i)]
  simp only [hmass, mul_one, ← symbolMean_eq_sum d v]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hm : (∑ i, 2 * (v i ^ 2 * d i) * symbolMean d v) = 2 * (symbolMean d v) ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← symbolMean_eq_sum d v]
    ring
  rw [hm, ← Finset.sum_mul, hmass, one_mul, symbolVariance_eq_moments d v hv]
  ring

/-- Adding a constant to every symbol leaves its fluctuation unchanged. -/
theorem symbolFluctuation_add_const (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) (c : ℝ) :
    symbolFluctuation (fun i => d i + c) v = symbolFluctuation d v := by
  have hm : symbolMean (fun i => d i + c) v = symbolMean d v + c := by
    have hd : diagonalColumn (fun i => d i + c) v = diagonalColumn d v + c • v := by
      funext i
      simp only [diagonalColumn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [symbolMean, hd, add_dotProduct, smul_dotProduct, smul_eq_mul, hv, mul_one]
  funext i
  simp only [symbolFluctuation, hm]
  ring

/-- Weighted symbol variance is invariant under a common scalar shift of the symbol. -/
theorem symbolVariance_add_const (d v : ι → ℝ) (hv : v ⬝ᵥ v = 1) (c : ℝ) :
    symbolVariance (fun i => d i + c) v = symbolVariance d v := by
  simp only [symbolVariance, symbolFluctuation_add_const d v hv c]

/-- The covariance is unchanged by removing the boundary column's parallel component. -/
theorem covariance_center (d v β : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    symbolFluctuation d v ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center β v = signedCovariance d v β := by
  simp only [Cvs.Approximant.ConnesErrorColumn.center, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    symbolFluctuation_dot d v hv, mul_zero, sub_zero, signedCovariance]

/-- The squared centered diagonal-plus-boundary column retains signed covariance. -/
theorem centered_sum_sq (d v β : ι → ℝ) (hv : v ⬝ᵥ v = 1) :
    Cvs.Approximant.ConnesErrorColumn.center (diagonalColumn d v + β) v ⬝ᵥ
      Cvs.Approximant.ConnesErrorColumn.center (diagonalColumn d v + β) v =
      symbolVariance d v + β ⬝ᵥ β - (β ⬝ᵥ v) ^ 2 + 2 * signedCovariance d v β := by
  have hc : Cvs.Approximant.ConnesErrorColumn.center (diagonalColumn d v + β) v =
      symbolFluctuation d v + Cvs.Approximant.ConnesErrorColumn.center β v := by
    funext i
    simp only [Cvs.Approximant.ConnesErrorColumn.center, hv, div_one, add_dotProduct, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, symbolFluctuation, symbolMean,
      diagonalColumn]
    ring
  rw [hc, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_comm (Cvs.Approximant.ConnesErrorColumn.center β v) (symbolFluctuation d v),
    covariance_center d v β hv, center_sq_unit β v hv]
  unfold symbolVariance
  ring

/-- A unit trial's residual for a diagonal-plus-boundary action has the exact covariance expansion. -/
theorem residual_diagonal_boundary (u d v β : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hu : u = diagonalColumn d v + β) :
    (u - (v ⬝ᵥ u) • v) ⬝ᵥ (u - (v ⬝ᵥ u) • v) =
      symbolVariance d v + β ⬝ᵥ β - (β ⬝ᵥ v) ^ 2 + 2 * signedCovariance d v β := by
  have hc : u - (v ⬝ᵥ u) • v = Cvs.Approximant.ConnesErrorColumn.center u v := by
    simp only [Cvs.Approximant.ConnesErrorColumn.center, hv, div_one, dotProduct_comm v u]
  rw [hc, hu, centered_sum_sq d v β hv]

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The actual diagonal window symbol on signed modes. -/
def symbolCoefficients (P R : ℕ) (L : ℝ) (N : ℕ) : Idx N → ℝ :=
  fun i => Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L)

/-- The actual symbol coefficients are even. -/
theorem symbolCoefficients_even (P R : ℕ) (L : ℝ) (N : ℕ) (i : Idx N) :
    symbolCoefficients P R L N (negI N i) = symbolCoefficients P R L N i := by
  simp only [symbolCoefficients, Cvs.Finite.SymmetricModeSet.mode_negI, Int.cast_neg]
  rw [show 2 * π * (-(mode N i : ℝ)) / L = -(2 * π * (mode N i : ℝ) / L) by ring]
  exact Cvs.Approximant.ConnesTailWeightedEnergy.symbolCut_neg P R L _

/-- The actual boundary column of an even vector is even. -/
theorem boundary_column_even {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hv : ∀ i, v (negI N i) = v i) (i : Idx N) :
    (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) (negI N i) =
      (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) i := by
  have hM := Cvs.Route.GroundRouteJointGap.mulVec_even (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.mode_negI N)) hv i
  rw [Cvs.Approximant.TailRetainedModeCoupling.matrix_eq_diagonal_add_boundary hL P R N, Matrix.add_mulVec] at hM
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, hv] at hM
  change symbolCoefficients P R L N (negI N i) * v i + _ =
    symbolCoefficients P R L N i * v i + _ at hM
  rw [symbolCoefficients_even] at hM
  linarith

/-- The full boundary column of an even unit trial obeys the order-independent squared budget. -/
theorem boundary_column_sq_le {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv : v ⬝ᵥ v = 1) :
    (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) ⬝ᵥ
      (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) ≤ (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L) ^ 2 := by
  have hsum : ∑ i, v i ^ 2 = 1 := by simpa only [dotProduct, sq] using hv
  have hb := Cvs.WeilForm.PhysicalCubicCorrectionColumn.column_sq_le_of_unit_pairing (negI N)
    (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) (boundary_column_even hL P R N v hve)
    (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L) (by
      intro f hf hunit
      rw [dotProduct_comm]
      have h := Cvs.WeilForm.EvenBoundaryKernelBound.boundary_bilinear_bound hL P R N f v hf hve
      simpa only [hunit, hsum, show (1 : ℝ) + 1 = 2 by norm_num,
        div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h)
  simpa only [dotProduct, sq] using hb

/-- The actual residual is symbol variance plus orthogonal boundary energy and signed covariance. -/
theorem residual_eq_variance_covariance {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hv : v ⬝ᵥ v = 1) :
    let d := symbolCoefficients P R L N
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R L N v =
      symbolVariance d v + β ⬝ᵥ β - (β ⬝ᵥ v) ^ 2 + 2 * signedCovariance d v β := by
  dsimp only
  unfold Cvs.Route.JointGapFromResidual.residualSq
  apply residual_diagonal_boundary _ _ _ _ hv
  rw [Cvs.Approximant.TailRetainedModeCoupling.matrix_eq_diagonal_add_boundary hL P R N, Matrix.add_mulVec]
  funext i
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, diagonalColumn, symbolCoefficients]

/-- The actual residual budget retains the parallel boundary subtraction and signed covariance. -/
theorem residual_le_variance_covariance {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv : v ⬝ᵥ v = 1) :
    let d := symbolCoefficients P R L N
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R L N v ≤
      symbolVariance d v + (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L) ^ 2 - (β ⬝ᵥ v) ^ 2
        + 2 * signedCovariance d v β := by
  dsimp only
  rw [residual_eq_variance_covariance hL P R N v hv]
  linarith [boundary_column_sq_le hL P R N v hve hv]

/-- The covariance budget applies to the constructed Connes trial at every positive window. -/
theorem connes_residual_le_variance_covariance {x : ℝ} (hx : 1 < x) (P R N : ℕ) :
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    let d := symbolCoefficients P R (Real.log x) N
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R (Real.log x) N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R (Real.log x) N v ≤
      symbolVariance d v + (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x)) ^ 2
        - (β ⬝ᵥ v) ^ 2 + 2 * signedCovariance d v β :=
  residual_le_variance_covariance (Real.log_pos hx) P R N _
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x)
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self (fun _ => N) x)

/-- A codimension-one floor and the signed variance budget supply the scaled joint gap. -/
theorem jointGap_of_variance_covariance {P R N : ℕ} {L K μ : ℝ} (hL : 0 < L)
    (kt v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ) (hK : 1 ≤ K)
    (hbudget : (K - 1) *
      (symbolVariance (symbolCoefficients P R L N) v + (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L) ^ 2
        - ((Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) ⬝ᵥ v) ^ 2
        + 2 * signedCovariance (symbolCoefficients P R L N) v
          (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v))
      ≤ (μ - v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)) ^ 2) :
    Cvs.Route.GroundRouteJointGap.JointGap P R L N K v := by
  apply Cvs.Route.JointGapFromResidual.jointGap_of_residual hL kt v hve hv hfloor hqμ hK
  exact (mul_le_mul_of_nonneg_left
    (residual_le_variance_covariance hL P R N v hve hv)
    (sub_nonneg.mpr hK)).trans hbudget

end Cvs.Approximant.ResidualSymbolVariance
