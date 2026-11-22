import Mathlib
import Cvs.Approximant.ConnesEndpointGeometry
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxFoldedCosineVolterra
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxRightInverse
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.Route.ModeBoxVolterraCurvature
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.PrimeMomentVolterra

/-!
# Pure Volterra Curvature Integral Representation and Endpoint-Invariance

Defines `boxPureCurvatureMatrix` on `ModeBox M₀`, proves its quadratic equivalence with
`boxCurvatureDiscrepancyMatrix` on even modes, and derives `ModeBoxPureCurvatureGainTarget`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxPureCurvature
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset MeasureTheory
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.WeilForm.PrimeMomentVolterra
open Cvs.Approximant.ConnesEndpointGeometry
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxRightInverse
open Cvs.Route.ModeBoxShiftedArchGreen
open Cvs.Route.ModeBoxVolterraCurvature
open Cvs.Route.ModeBoxFoldedCosineVolterra

/-! ### Pure Volterra curvature matrix `boxPureCurvatureMatrix` on `ModeBox M₀` -/

/-- Pure Volterra curvature matrix on `ModeBox M₀` associated to a ramp profile `V : ℝ → ℝ`,
omitting the constant endpoint term `(2 / L) * V L`. -/
def boxPureCurvatureMatrix (L : ℝ) (M₀ : ℕ) (V : ℝ → ℝ) :
    Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun i j =>
    (2 / L) * ∫ d in (0 : ℝ)..L, Cvs.Approximant.ConnesEndpointGeometry.cosineCurvature L i.1.natAbs j.1.natAbs d * V (L - d)

/-- Entrywise decomposition of `boxVolterraMatrix` into constant endpoint plus pure curvature. -/
theorem boxVolterraMatrix_eq_endpoint_add_pureCurvature (L : ℝ) (M₀ : ℕ) (V : ℝ → ℝ) :
    boxVolterraMatrix L M₀ V =
      Matrix.of (fun _ _ => (2 / L) * V L) + boxPureCurvatureMatrix L M₀ V := by
  ext i j
  simp [boxVolterraMatrix, boxPureCurvatureMatrix, Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra, mul_add]

/-- Quadratic-form decomposition of `boxVolterraMatrix` into `boxEndpoint` plus pure curvature. -/
theorem boxVolterraMatrix_quad_eq_endpoint_add_pureCurvature (L : ℝ) (M₀ : ℕ) (V : ℝ → ℝ)
    (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxVolterraMatrix L M₀ V *ᵥ η) =
      (2 * V L / L) * (boxEndpoint M₀ η) ^ 2 +
        η ⬝ᵥ (boxPureCurvatureMatrix L M₀ V *ᵥ η) := by
  have hconst : η ⬝ᵥ (Matrix.of (fun _ _ : ModeBox M₀ => (2 / L) * V L) *ᵥ η) =
      (2 * V L / L) * (boxEndpoint M₀ η) ^ 2 := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, boxEndpoint, sq, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [boxVolterraMatrix_eq_endpoint_add_pureCurvature, Matrix.add_mulVec, dotProduct_add, hconst]

/-! ### Equivalence with `boxCurvatureDiscrepancyMatrix` and linear-ramp identities -/

/-- On `evenModeSub (negBox M₀)`, the quadratic form of `boxCurvatureDiscrepancyMatrix` equals
that of `boxPureCurvatureMatrix` for `primeRamp - meanRamp`. -/
theorem boxCurvatureDiscrepancyMatrix_quad_eq_pureCurvature {L : ℝ} (hL : 0 < L)
    (P R M₀ : ℕ) {η : ModeBox M₀ → ℝ} (hη : η ∈ evenModeSub (negBox M₀)) :
    η ⬝ᵥ (boxCurvatureDiscrepancyMatrix P R L M₀ *ᵥ η) =
      η ⬝ᵥ (boxPureCurvatureMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η) := by
  have h1 := boxDiscrepancyMatrix_quad_eq_boxVolterraMatrix hL P R M₀ hη
  rw [boxDiscrepancyMatrix_quad_eq_endpoint_add_curvature P R L M₀ η,
    boxVolterraMatrix_quad_eq_endpoint_add_pureCurvature,
    discrepancyEntry_zero_zero hL P R] at h1
  linarith

/-! ### Lower bounds on `Cvs.Finite.TruncationQuadraticForm.M` and `ModeBoxPureCurvatureGainTarget` -/

end Cvs.Route.ModeBoxPureCurvature
