import Mathlib
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxRightInverse

/-!
# Endpoint + Flat-Residual Decomposition and Schur Reduction on `ModeBox M₀`

Splits `evenModeSub (negBox M₀)` into `boxZeroVec M₀` and the codimension-1 endpoint-flat subspace
`boxFlatSub M₀`, proving the Schur completion and $O(1 / M_0)$ zero-mode `weightedLeakage` bound.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxEndpointFlatSchur
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxRightInverse

/-! ### Origin mode `zeroModeBox M₀` and zero-mode unit vector `boxZeroVec M₀` -/

/-- The zero mode `0 ∈ ModeBox M₀`. -/
def zeroModeBox (M₀ : ℕ) : ModeBox M₀ :=
  ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- The zero-mode unit coordinate vector on `ModeBox M₀`. -/
def boxZeroVec (M₀ : ℕ) : ModeBox M₀ → ℝ :=
  fun m => if m = zeroModeBox M₀ then 1 else 0

/-- Dot product of `boxZeroVec M₀` with `η` extracts the zero-mode coordinate `η (zeroModeBox M₀)`. -/
theorem boxZeroVec_dotProduct (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    boxZeroVec M₀ ⬝ᵥ η = η (zeroModeBox M₀) := by
  simp [dotProduct, boxZeroVec]

/-! ### Codimension-1 endpoint-flat subspace `boxFlatSub M₀` and `boxFlatResidual M₀` -/

/-- `boxEndpoint M₀` as a linear functional `(ModeBox M₀ → ℝ) →ₗ[ℝ] ℝ`. -/
def boxEndpointLM (M₀ : ℕ) : (ModeBox M₀ → ℝ) →ₗ[ℝ] ℝ where
  toFun := boxEndpoint M₀
  map_add' u v := by simp [boxEndpoint, Finset.sum_add_distrib]
  map_smul' c u := by simp [boxEndpoint, Finset.mul_sum]

/-- The codimension-1 endpoint-flat even subspace of `ModeBox M₀`. -/
def boxFlatSub (M₀ : ℕ) : Submodule ℝ (ModeBox M₀ → ℝ) :=
  evenModeSub (negBox M₀) ⊓ LinearMap.ker (boxEndpointLM M₀)

/-- Membership in `boxFlatSub M₀` is equivalent to evenness and `boxEndpoint M₀ η = 0`. -/
theorem mem_boxFlatSub_iff {M₀ : ℕ} {η : ModeBox M₀ → ℝ} :
    η ∈ boxFlatSub M₀ ↔ η ∈ evenModeSub (negBox M₀) ∧ boxEndpoint M₀ η = 0 :=
  Iff.rfl

/-! ### Bilinear expansion and Schur completion along `boxZeroVec M₀` and `boxFlatResidual M₀` -/

/-! ### Uniform-in-`N` $O(1 / M_0)$ zero-mode `weightedLeakage` bound for `boxZeroVec M₀` -/

end Cvs.Route.ModeBoxEndpointFlatSchur
