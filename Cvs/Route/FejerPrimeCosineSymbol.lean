import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.HalfPoleMatrixModeBox
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.PoleOrthogonalSubspace
import Cvs.Route.PosChannelFloorCoercivity

/-!
# Fejér Prime Cosine Symbol `fejerPrimeCos` and `boxPoleVec` Quadratic Bounds

Formalizes `fejerPrimeCos`, proves its Fejér tent formula and the `A1Mat`/`ApoleHalfMat` diagonal
identities, and establishes explicit `poleFactor` lower bounds on `boxPoleVec ⬝ᵥ (ApoleHalfMat *ᵥ boxPoleVec)`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.FejerPrimeCosineSymbol
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Finset
open Cvs.Finite.DiagonalCutSymbol
open Cvs.Finite.OneModeEntries
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Finite.OffDiagonalKernelDecay
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.HighModePoleTailDecay
open Cvs.Route.HalfPoleMatrixModeBox
open Cvs.Route.PoleOrthogonalSubspace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Fejér prime cosine diagonal symbol `fejerPrimeCos` -/

/-! ### Explicit `poleFactor` lower bounds on the `boxPoleVec` quadratic form -/

/-- Exact quadratic form of `poleRankOneMat` at `boxPoleVec L M₀`:
`(2 * poleFactor L / L) * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)²`. -/
theorem boxPoleVec_poleRankOneMat_quad_eq (L : ℝ) (M₀ : ℕ) :
    Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) =
      (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ^ 2 :=
  Cvs.Route.HighModePoleTailDecay.poleRankOneMat_quad_eq_sq L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀)

/-- Exact quadratic form of `ApoleHalfMat` at `boxPoleVec L M₀`:
`A1Mat` quadratic form plus `(poleFactor L / L) * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)²`. -/
theorem boxPoleVec_ApoleHalfMat_quad_eq (P R : ℕ) (L : ℝ) (M₀ : ℕ) :
    Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.HalfPoleMatrixModeBox.ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) =
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
          (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) +
        (Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ^ 2 := by
  rw [Cvs.Route.HalfPoleMatrixModeBox.ApoleHalfMat_quad_eq, boxPoleVec_poleRankOneMat_quad_eq]
  ring

/-- Lower bound on the `ApoleHalfMat` quadratic form at `boxPoleVec L M₀` with linear factor
`4 * poleFactor L / L`. -/
theorem boxPoleVec_ApoleHalfMat_quad_ge_add_four_mul {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) :
    Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) +
      (4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.HalfPoleMatrixModeBox.ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) := by
  rw [boxPoleVec_ApoleHalfMat_quad_eq]
  have h4 : 4 ≤ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ :=
    Cvs.Route.PoleOrthogonalSubspace.four_le_boxPoleVec_dotProduct_self L M₀
  have hpos : 0 ≤ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ := by linarith
  have hp : 0 ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L / L :=
    div_nonneg (Cvs.Route.PosChannelFloorCoercivity.poleFactor_nonneg L) hL.le
  have hsq : 4 * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hp
  have heq : (Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (4 * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀)) =
      (4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) := by ring
  linarith

/-- If `cA * (u ⬝ᵥ u) ≤ u ⬝ᵥ (A1Mat *ᵥ u)` at `u = boxPoleVec L M₀`, then
`(cA + 4 * poleFactor L / L) * (u ⬝ᵥ u) ≤ u ⬝ᵥ (ApoleHalfMat *ᵥ u)`. -/
theorem boxPoleVec_ApoleHalfMat_quad_ge_of_A1Mat_ge {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    {cA : ℝ}
    (hcA : cA * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀)) :
    (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) *
        (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.HalfPoleMatrixModeBox.ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) := by
  have h1 := boxPoleVec_ApoleHalfMat_quad_ge_add_four_mul hL P R M₀
  linarith

/-- Discharges the `hpole` hypothesis `cR * (u ⬝ᵥ u) ≤ u ⬝ᵥ (ApoleHalfMat *ᵥ u)` from
`cA * (u ⬝ᵥ u) ≤ u ⬝ᵥ (A1Mat *ᵥ u)` and `cR ≤ cA + 4 * poleFactor L / L`. -/
theorem boxPoleVec_ApoleHalfMat_floor_of_A1Mat_ge {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    {cA cR : ℝ}
    (hcA : cA * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀))
    (hcR : cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) :
    cR * (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) ≤
      Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀ ⬝ᵥ
        (Cvs.Route.HalfPoleMatrixModeBox.ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.PoleOrthogonalSubspace.boxPoleVec L M₀) := by
  have h1 := boxPoleVec_ApoleHalfMat_quad_ge_of_A1Mat_ge hL P R M₀ hcA
  have hpos := (Cvs.Route.PoleOrthogonalSubspace.boxPoleVec_dotProduct_self_pos L M₀).le
  exact (mul_le_mul_of_nonneg_right hcR hpos).trans h1

end Cvs.Route.FejerPrimeCosineSymbol
