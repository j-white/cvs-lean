import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.WeilForm.ArithmeticFloorAboveBand

/-!
# Unconditional `(2M₀ + 1)`-Free Damped `ModeBox M₀` Reduction

Bridges `Cvs.WeilForm.PrimeDiagonalBulkSchur.damped_low_high_lower` to `modeCutoffRung N M₀` and `ModeBox M₀`, yielding an
`∀ N`-free and `(2M₀ + 1)`-free `ModeBox M₀` reduction for `RiemannHypothesis`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxDampedReduction
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.ArithmeticFloorAboveBand
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.HighModePoleTailDecay

/-! ### Shifted-diagonal quadratic form and low-mode diagonal deficit on `ModeBox M₀` -/

/-! ### Isometric transfer of the shifted-diagonal and `positiveRemainder` quadratic forms -/

/-! ### Bridging `Cvs.WeilForm.PrimeDiagonalBulkSchur.damped_low_high_lower` to `modeCutoffRung N M₀` and `Bulk` -/

/-- Pointwise disjointness `r i * w i = 0` for `r ∈ modeCutoffRung N M₀` and
`w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`. -/
theorem modeCutoffRung_mul_bulk_eq_zero {N M₀ : ℕ} {r w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : r ∈ modeCutoffRung N M₀)
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w)
    (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    r i * w i = 0 := by
  by_cases hi : i ∈ modeCutoffSet N M₀
  · simp [Cvs.Route.HighModePoleTailDecay.apply_eq_zero_of_mem_modeCutoffSet hw hi]
  · simp [Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hi]

/-- Any `w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)` vanishes at frequencies `< T`
whenever `Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ M₀ + 1`. -/
theorem bulk_apply_eq_zero_of_freq_lt {L T : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ M₀ + 1) {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w)
    (i : Cvs.Finite.SymmetricModeSet.Idx N) (hfreq : |2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L| < T) :
    w i = 0 := by
  refine Cvs.Route.HighModePoleTailDecay.apply_eq_zero_of_mem_modeCutoffSet hw ?_
  change (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
  by_contra hnot
  have hge : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs := by omega
  exact hfreq.not_ge (Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder_frequency hL T (Cvs.Finite.SymmetricModeSet.mode N i) hge)

/-! ### `∀ N`-free and `(2M₀ + 1)`-free `ModeBox M₀` positivity theorems and target -/

end Cvs.Route.ModeBoxDampedReduction
