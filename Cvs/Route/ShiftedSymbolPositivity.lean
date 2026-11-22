import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant

/-!
# Universal Positivity Threshold for `shiftedArchSymbol` and Core Energy Reduction

Establishes the universal threshold `shiftedSymbolPosThreshold = √(27 / truncConst 4)` above which
`0 ≤ shiftedArchSymbol t` and reduces `-coreDeficit` on `ModeBox M₀` to `boxUniversalCoreEnergy`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ShiftedSymbolPositivity
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer

/-! ### Explicit `27 / t²` tail bound for the three intermediate Lévy channels `k = 1, 2, 3` -/

/-- For `t ≠ 0`, each Lévy channel satisfies `2 * uu (bk k) t ≤ 2 * bk k / t²`. -/
theorem two_mul_uu_bk_le_div_sq (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t ≤ 2 * Cvs.Finite.WindowMatrixSymbolKernel.bk k / t ^ 2 := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
  have hb : 0 < Cvs.Finite.WindowMatrixSymbolKernel.bk k := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hden : t ^ 2 ≤ (Cvs.Finite.WindowMatrixSymbolKernel.bk k) ^ 2 + t ^ 2 := by nlinarith
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_left (by positivity) ht2 hden

/-- The sum `∑_{k=1}^3 2 b_k = 5 + 9 + 13` equals `27`. -/
theorem sum_Ico_two_mul_bk :
    (∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.bk k) = 27 := by
  norm_num [Finset.sum_Ico_succ_top, Cvs.Finite.WindowMatrixSymbolKernel.bk]

/-- For `t ≠ 0`, the three intermediate Lévy channels sum to at most `27 / t²`. -/
theorem sum_Ico_two_mul_uu_le_twenty_seven_div_sq {t : ℝ} (ht : t ≠ 0) :
    (∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t) ≤ 27 / t ^ 2 := by
  calc ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t
      ≤ ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.bk k / t ^ 2 :=
        Finset.sum_le_sum fun k _ => two_mul_uu_bk_le_div_sq k ht
    _ = (∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.bk k) / t ^ 2 := by rw [← Finset.sum_div]
    _ = 27 / t ^ 2 := by rw [sum_Ico_two_mul_bk]

/-! ### Universal frequency thresholds `shiftedSymbolPosThreshold` and `shiftedSymbolHalfFloorThreshold` -/

/-- Universal frequency threshold `√(27 / truncConst 4)` where `shiftedArchSymbol` becomes nonnegative. -/
def shiftedSymbolPosThreshold : ℝ :=
  Real.sqrt (27 / Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4)

/-- Universal frequency threshold `√(54 / truncConst 4)` where `shiftedArchSymbol ≥ truncConst 4 / 2`. -/
def shiftedSymbolHalfFloorThreshold : ℝ :=
  Real.sqrt (54 / Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4)

/-- `shiftedSymbolPosThreshold` is strictly positive. -/
theorem shiftedSymbolPosThreshold_pos : 0 < shiftedSymbolPosThreshold := by
  unfold shiftedSymbolPosThreshold
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos)

/-- `shiftedSymbolHalfFloorThreshold` is strictly positive. -/
theorem shiftedSymbolHalfFloorThreshold_pos : 0 < shiftedSymbolHalfFloorThreshold := by
  unfold shiftedSymbolHalfFloorThreshold
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos)

/-- `shiftedSymbolPosThreshold ≤ shiftedSymbolHalfFloorThreshold`. -/
theorem shiftedSymbolPosThreshold_le_halfFloorThreshold :
    shiftedSymbolPosThreshold ≤ shiftedSymbolHalfFloorThreshold := by
  unfold shiftedSymbolPosThreshold shiftedSymbolHalfFloorThreshold
  exact Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right (by norm_num) Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos.le)

/-- Exact square of `shiftedSymbolPosThreshold`. -/
theorem shiftedSymbolPosThreshold_sq :
    shiftedSymbolPosThreshold ^ 2 = 27 / Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 := by
  unfold shiftedSymbolPosThreshold
  exact Real.sq_sqrt (div_nonneg (by norm_num) Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos.le)

/-- Exact square of `shiftedSymbolHalfFloorThreshold`. -/
theorem shiftedSymbolHalfFloorThreshold_sq :
    shiftedSymbolHalfFloorThreshold ^ 2 = 54 / Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 := by
  unfold shiftedSymbolHalfFloorThreshold
  exact Real.sq_sqrt (div_nonneg (by norm_num) Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos.le)

/-! ### Universal low-mode core energy `boxUniversalCoreEnergy` and high-mode cushion on `ModeBox M₀` -/

/-- Universal low-mode core energy on `ModeBox M₀` restricted to `|ω_m| < shiftedSymbolPosThreshold`. -/
def boxUniversalCoreEnergy (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : ModeBox M₀,
    if |2 * π * (boxMode M₀ m : ℝ) / L| < shiftedSymbolPosThreshold then (η m) ^ 2 else 0

/-- Universal high-mode energy on `ModeBox M₀` above `shiftedSymbolHalfFloorThreshold`. -/
def boxUniversalHighEnergy (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : ModeBox M₀,
    if shiftedSymbolHalfFloorThreshold ≤ |2 * π * (boxMode M₀ m : ℝ) / L| then (η m) ^ 2 else 0

/-! ### `ModeBoxUniversalCoreDiscrepancyTarget` and route to `RiemannHypothesis` -/

end Cvs.Route.ShiftedSymbolPositivity
