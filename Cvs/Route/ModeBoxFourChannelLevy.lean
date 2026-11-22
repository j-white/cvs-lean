import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.SymbolPartialFraction
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.Zeta.Digamma

/-!
# Four-Channel Lévy Truncation Positivity and Multi-Channel Shifted Symbol on `ModeBox M₀`

Connects `Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos` (`0 < Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4`) and `Cvs.WeilForm.Archimedean.TruncationBelowSymbol` to `ModeBox M₀`,
isolating the three intermediate Lévy channels `k = 1, 2, 3` from `multiShiftedArchSymbol 4`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxFourChannelLevy
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
open Cvs.WeilForm.Archimedean.OffWindowDefect
open Cvs.WeilForm.Archimedean.SymbolPartialFraction
open Cvs.WeilForm.Archimedean.TruncationBelowSymbol
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.WeilForm.GreenRemovesFirstArchChannel
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxShiftedArchGreen

/-! ### Bridge between `Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx` and `Cvs.Finite.WindowMatrixSymbolKernel.bk` / `Cvs.Finite.WindowMatrixSymbolKernel.uu` -/

/-- Each rational pole term `2 b_k / (t² + b_k²)` in `Cvs.WeilForm.Archimedean.SymbolPartialFraction` equals `2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t`. -/
theorem two_mul_bIdx_div_eq_two_mul_uu (k : ℕ) (t : ℝ) :
    2 * Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k / (t ^ 2 + (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) ^ 2) = 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t := by
  unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx Cvs.Finite.WindowMatrixSymbolKernel.bk Cvs.Finite.WindowMatrixSymbolKernel.uu
  rw [add_comm (t ^ 2)]
  ring

/-! ### The `N`-channel shifted Archimedean symbol and `N = 4` positivity -/

/-- The Archimedean symbol with the first `N` Lévy pole channels cancelled. -/
def multiShiftedArchSymbol (N : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t + ∑ k ∈ Finset.range N, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t

/-- Exact identity relating `multiShiftedArchSymbol N t` to `Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N` and
the shifted digamma difference (`Cvs.WeilForm.Archimedean.SymbolPartialFraction.archSymbol_split`). -/
theorem multiShiftedArchSymbol_eq_truncSymbol_add_remainder (N : ℕ) (t : ℝ) :
    multiShiftedArchSymbol N t =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N +
        ((Complex.digamma (Cvs.Zeta.digammaArg t N)).re -
          (Complex.digamma (Cvs.Zeta.digammaArg 0 N)).re) := by
  unfold multiShiftedArchSymbol
  rw [Cvs.WeilForm.Archimedean.SymbolPartialFraction.archSymbol_split t N]
  have hsum : (∑ n ∈ Finset.range N, 2 * Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx n / (t ^ 2 + (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx n) ^ 2)) =
      ∑ k ∈ Finset.range N, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t :=
    Finset.sum_congr rfl fun k _ => two_mul_bIdx_div_eq_two_mul_uu k t
  linarith

/-- Exact digamma-deficit tail series representation of `multiShiftedArchSymbol N t`. -/
theorem multiShiftedArchSymbol_eq_truncConst_add_tsum (N : ℕ) (t : ℝ) :
    multiShiftedArchSymbol N t =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N + ∑' k : ℕ, Cvs.Zeta.digammaDeficit t (k + N) := by
  rw [multiShiftedArchSymbol_eq_truncSymbol_add_remainder N t, Cvs.WeilForm.Archimedean.TruncationBelowSymbol.remainder_eq t N]

/-- At `N = 1`, `multiShiftedArchSymbol 1` coincides with `Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol`. -/
theorem multiShiftedArchSymbol_one_eq (t : ℝ) :
    multiShiftedArchSymbol 1 t = Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t := by
  unfold multiShiftedArchSymbol Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier
    Cvs.Finite.WindowMatrixSymbolKernel.uu Cvs.Finite.WindowMatrixSymbolKernel.bk
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add]
  have hpos : (0 : ℝ) < (1 / 2) ^ 2 + t ^ 2 := by positivity
  have hpos2 : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
  field_simp
  ring

/-- **Exact channel split between `shiftedArchSymbol` (`N = 1`) and `multiShiftedArchSymbol 4`**:
isolates the three intermediate Lévy channels `k ∈ {1, 2, 3}`. -/
theorem shiftedArchSymbol_eq_multi_four_sub_Ico (t : ℝ) :
    Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t =
      multiShiftedArchSymbol 4 t - ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t := by
  rw [← multiShiftedArchSymbol_one_eq t]
  unfold multiShiftedArchSymbol
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t) (by decide : 1 ≤ 4)
  linarith

/-! ### Lifting `multiShiftedArchSymbol` and the 3-channel residual to `ModeBox M₀` -/

/-- Diagonal matrix of `multiShiftedArchSymbol N` on `ModeBox M₀`. -/
def boxMultiShiftedDiag (N : ℕ) (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  Matrix.diagonal (fun m : ModeBox M₀ =>
    multiShiftedArchSymbol N (2 * π * (boxMode M₀ m : ℝ) / L))

/-- Diagonal quadratic energy of the three intermediate Lévy channels `k = 1, 2, 3` on `ModeBox M₀`. -/
def boxResidualLevyDiagQ (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : ModeBox M₀,
    (∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ m : ℝ) / L)) *
      (η m) ^ 2

/-- **Exact decomposition of `boxShiftedDiag` into `boxMultiShiftedDiag 4` minus `boxResidualLevyDiagQ`.** -/
theorem boxShiftedDiag_quad_eq_multi_four_sub_residual (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxShiftedDiag L M₀ *ᵥ η) =
      η ⬝ᵥ (boxMultiShiftedDiag 4 L M₀ *ᵥ η) - boxResidualLevyDiagQ L M₀ η := by
  simp only [dotProduct, Matrix.mulVec_diagonal, boxShiftedDiag, boxMultiShiftedDiag,
    boxResidualLevyDiagQ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [shiftedArchSymbol_eq_multi_four_sub_Ico (2 * π * (boxMode M₀ m : ℝ) / L)]
  ring

/-! ### `ModeBoxFourChannelFloorTarget` and reduction to `ModeBoxWeightedLeakageTarget` -/

end Cvs.Route.ModeBoxFourChannelLevy
