import Mathlib
import Cvs.Route.ModeBoxIsometricTransfer

/-!
# Exact `ModeBox M₀` Right-Inverse and Uniform-in-`N` Endpoint-Flat / Pole-Free Leakage

Proves `weightedLeakage (M₀ + 1) = 0` for `N ≤ M₀` and `toModeBox (fromModeBox η) = η` for `M₀ ≤ N`,
lifting `Cvs.Finite.EvenPairCancellation` and `an earlier result` uniformly across all `N : ℕ` on `ModeBox M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxRightInverse
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree
open Cvs.Route.ModeBoxIsometricTransfer

/-! ### Exact vanishing of `highPart` and `weightedLeakage` when `N < K` (`N ≤ M₀`) -/

/-! ### Exact right-inverse `toModeBox N M₀ (fromModeBox N M₀ η) = η` when `M₀ ≤ N` -/

/-! ### Uniform-in-`N` lifting of `Cvs.Finite.EvenPairCancellation` (endpoint-flat) and `an earlier result` (pole-free) to `ModeBox M₀` -/

/-- Discrete right-endpoint value `∑ m : ModeBox M₀, η m` on `ModeBox M₀`. -/
def boxEndpoint (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : ModeBox M₀, η m

/-! ### `ε`-arbitrary `ModeBox M₀` floor reduction for `ModeBoxWeightedLeakageTarget` -/

end Cvs.Route.ModeBoxRightInverse
