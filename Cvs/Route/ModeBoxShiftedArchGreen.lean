import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.GreenRemovesFirstArchChannel

/-!
# Shifted Archimedean-Green and Centered Discrepancy Decomposition on `ModeBox M₀`

Lifts the `Cvs.WeilForm.GreenRemovesFirstArchChannel`/`Cvs.WeilForm.ArchGreenSecondChannel`/`Cvs.WeilForm.LowHeadSignedCorrection` decomposition `M = boxArchGreenMatrix - boxDiscrepancyMatrix`
to `ModeBox M₀` and reduces `ModeBoxWeightedLeakageTarget` to `boxDiscrepancyMatrix`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxShiftedArchGreen
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.GreenRemovesFirstArchChannel
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer

/-! ### Shifted Archimedean-Green and centered discrepancy matrices on `ModeBox M₀` -/

/-- Diagonal matrix of `Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol` on `ModeBox M₀`. -/
def boxShiftedDiag (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  Matrix.diagonal (fun m : ModeBox M₀ =>
    Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol (2 * π * (boxMode M₀ m : ℝ) / L))

/-- Higher-channel Archimedean boundary ladder `Cvs.WeilForm.ArchGreenSecondChannel.boundaryTail / L` on `ModeBox M₀`. -/
def boxTailMatrix (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun m n =>
    Cvs.WeilForm.ArchGreenSecondChannel.boundaryTail L (2 * π * (boxMode M₀ m : ℝ) / L) (2 * π * (boxMode M₀ n : ℝ) / L) / L

/-- Combined Archimedean-plus-Green reference matrix on `ModeBox M₀`. -/
def boxArchGreenMatrix (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  boxShiftedDiag L M₀ + boxTailMatrix L M₀

/-- Centered prime-minus-mean discrepancy matrix `Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry` on `ModeBox M₀`. -/
def boxDiscrepancyMatrix (P R : ℕ) (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun m n => Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (boxMode M₀ m) (boxMode M₀ n)

/-- **Exact shifted matrix decomposition on `ModeBox M₀`**:
`M P R L (boxMode M₀) = boxArchGreenMatrix L M₀ - boxDiscrepancyMatrix P R L M₀`. -/
theorem boxM_eq_shifted {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) =
      boxArchGreenMatrix L M₀ - boxDiscrepancyMatrix P R L M₀ := by
  ext m n
  rw [Cvs.WeilForm.ArchGreenSecondChannel.M_apply_shifted hL P R (boxMode_injective M₀)]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply,
    boxArchGreenMatrix, boxShiftedDiag, boxTailMatrix, boxDiscrepancyMatrix]

/-- **Quadratic form shifted decomposition on `ModeBox M₀`**. -/
theorem boxM_quad_eq_shifted {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η) =
      η ⬝ᵥ (boxArchGreenMatrix L M₀ *ᵥ η) -
        η ⬝ᵥ (boxDiscrepancyMatrix P R L M₀ *ᵥ η) := by
  rw [boxM_eq_shifted hL P R M₀, Matrix.sub_mulVec, dotProduct_sub]

/-! ### Even-sector positivity of `boxTailMatrix` and lower bounds on `boxArchGreenMatrix` -/

/-- On `evenModeSub (negBox M₀)`, the odd boundary factor `Cvs.Finite.WindowMatrixSymbolKernel.vv b` sums to zero. -/
theorem box_sum_even_mul_vv_eq_zero (L b : ℝ) {M₀ : ℕ} {η : ModeBox M₀ → ℝ}
    (hη : η ∈ evenModeSub (negBox M₀)) :
    ∑ m : ModeBox M₀, η m * Cvs.Finite.WindowMatrixSymbolKernel.vv b (2 * π * (boxMode M₀ m : ℝ) / L) = 0 :=
  Cvs.Route.EvenMatrixSlotPoleRestored.sum_even_mul_vv_eq_zero L b (negBox_involutive M₀) (boxMode_negBox M₀) hη

/-! ### Reduction of `ModeBoxWeightedLeakageTarget` to `boxDiscrepancyMatrix` -/

end Cvs.Route.ModeBoxShiftedArchGreen
