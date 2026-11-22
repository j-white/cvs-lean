import Mathlib
import Cvs.Approximant.ConnesEndpointGeometry
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxRightInverse
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.PrimeMomentVolterra

/-!
# Endpoint-Centered Volterra Curvature Decomposition and Corner Identity on `ModeBox M₀`

Isolates the endpoint ramp `Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 * (boxEndpoint M₀ η) ^ 2` from the
pure Volterra curvature matrix `boxCurvatureDiscrepancyMatrix` on `ModeBox M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxVolterraCurvature
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.GreenRemovesFirstArchChannel
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.WeilForm.PrimeMomentVolterra
open Cvs.Approximant.ConnesEndpointGeometry
open Cvs.WeilForm.MatrixPSDCriterion
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxRightInverse
open Cvs.Route.ModeBoxShiftedArchGreen

/-! ### Exact zero-mode discrepancy entry and `Cvs.WeilForm.MatrixPSDCriterion` corner identity on `ModeBox M₀` -/

/-- **Exact identity for `Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0`** as twice the endpoint ramp
divided by `L` (`Cvs.Approximant.ConnesEndpointGeometry.folded_discrepancyEntry_eq_signedMoment`, `Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra_zero`). -/
theorem discrepancyEntry_zero_zero {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 =
      2 * (Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R L - Cvs.WeilForm.PrimeMomentVolterra.meanRamp L) / L := by
  have h := Cvs.Approximant.ConnesEndpointGeometry.folded_discrepancyEntry_eq_signedMoment hL P R 0 0
  rw [Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra_zero] at h
  simp only [Nat.cast_zero, neg_zero] at h
  have hL0 : L ≠ 0 := hL.ne'
  rw [eq_div_iff hL0]
  linarith

/-! ### Symmetry of `boxDiscrepancyMatrix` and `discrepancyEntry` -/

/-! ### Endpoint-centered Volterra curvature matrix `boxCurvatureDiscrepancyMatrix` -/

/-- **Endpoint-centered (pure Volterra curvature) discrepancy matrix on `ModeBox M₀`**:
subtracts the constant zero-mode endpoint entry `Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0` from every pair. -/
def boxCurvatureDiscrepancyMatrix (P R : ℕ) (L : ℝ) (M₀ : ℕ) :
    Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun m n => Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (boxMode M₀ m) (boxMode M₀ n) -
    Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0

/-- **Exact splitting of `boxDiscrepancyMatrix` into the rank-1 endpoint ramp plus pure curvature**:
`ηᵀ D η = D₀₀ * (boxEndpoint M₀ η)² + ηᵀ D_curv η`. -/
theorem boxDiscrepancyMatrix_quad_eq_endpoint_add_curvature
    (P R : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxDiscrepancyMatrix P R L M₀ *ᵥ η) =
      Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 * (boxEndpoint M₀ η) ^ 2 +
        η ⬝ᵥ (boxCurvatureDiscrepancyMatrix P R L M₀ *ᵥ η) := by
  have h1 : η ⬝ᵥ (boxCurvatureDiscrepancyMatrix P R L M₀ *ᵥ η) =
      (∑ m : ModeBox M₀, ∑ n : ModeBox M₀,
        η m * (Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (boxMode M₀ m) (boxMode M₀ n) * η n)) -
      ∑ m : ModeBox M₀, ∑ n : ModeBox M₀,
        η m * (Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 * η n) := by
    simp only [dotProduct, Matrix.mulVec, boxCurvatureDiscrepancyMatrix,
      sub_mul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  have h2 : (∑ m : ModeBox M₀, ∑ n : ModeBox M₀,
      η m * (Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 * η n)) =
      Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L 0 0 * (boxEndpoint M₀ η) ^ 2 := by
    simp only [boxEndpoint, sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [h1, h2]
  dsimp [dotProduct, Matrix.mulVec, boxDiscrepancyMatrix]
  simp only [Finset.mul_sum]
  ring

end Cvs.Route.ModeBoxVolterraCurvature
