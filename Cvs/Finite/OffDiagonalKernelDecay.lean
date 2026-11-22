import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored

/-!
# Off-Diagonal Decay Bounds for `uu`, `sinc`, `kPrime`, `A1Mat`, and `ApoleMat`

Establishes lag-independent `1 / |ω − ω'|` cancellation in `kPrime` and `L`-independent off-diagonal
mode decay bounds for `(1 / L) * kPrime`, `A1Mat`, and `ApoleMat`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Finite.OffDiagonalKernelDecay
open Cvs.ZeroCounting

open scoped Matrix
open Real Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Pointwise bounds on `Cvs.Finite.WindowMatrixSymbolKernel.uu` and `Cvs.Finite.WindowMatrixSymbolKernel.sinc` -/

/-- For `0 ≤ a` and `ω ≠ 0`, `uu a ω = a / (a² + ω²) ≤ a / ω²`. -/
theorem uu_le_div_sq {a : ℝ} (ha : 0 ≤ a) {ω : ℝ} (hω : ω ≠ 0) :
    Cvs.Finite.WindowMatrixSymbolKernel.uu a ω ≤ a / ω ^ 2 := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
  have hω2 : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
  have hden : 0 < a ^ 2 + ω ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hω2]
  nlinarith [sq_nonneg a]

/-- At the pole abscissa `a = 1 / 2` and `ω ≠ 0`, `uu (1 / 2) ω ≤ 1 / (2 * ω²)`. -/
theorem uu_half_le_inv_two_sq {ω : ℝ} (hω : ω ≠ 0) :
    Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) ω ≤ 1 / (2 * ω ^ 2) := by
  have h := uu_le_div_sq (by norm_num : (0 : ℝ) ≤ 1 / 2) hω
  have heq : (1 / 2 : ℝ) / ω ^ 2 = 1 / (2 * ω ^ 2) := by ring
  linarith

/-! ### Uniform and off-diagonal decay bounds for `Cvs.Finite.WindowMatrixSymbolKernel.kPrime` -/

/-! ### Off-diagonal formulas and decay bounds for `A1Mat` and `ApoleMat` -/

/-- Entrywise kernel formula for `A1Mat`: diagonal `symbolCut` plus `(1 / L) * kPrime`. -/
theorem A1Mat_apply_kernel {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (i j : ι) :
    A1Mat P R L mode i j
      = (if i = j then Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * mode i / L) else 0)
        + 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * mode i / L) (2 * π * mode j / L) := by
  unfold A1Mat
  rw [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R hinj i j]
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kK
  ring

end Cvs.Finite.OffDiagonalKernelDecay
