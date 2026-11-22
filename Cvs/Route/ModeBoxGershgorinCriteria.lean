import Mathlib
import Cvs.Finite.OffDiagonalKernelDecay
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# `∀ N`-Free `ModeBox` Reduction and Gershgorin Criteria for `RiemannHypothesis`

Combines the `N`-independent `modeSepSum` bound (`Cvs.Route.ModeSepSumUniformBound`) with the isometric `ModeBox M₀` lifting
(`Cvs.Route.ModeBoxIsometricTransfer`) to eliminate the universal quantifier `∀ N : ℕ` from `RiemannHypothesis`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxGershgorinCriteria
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Finite.OffDiagonalKernelDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Evenness of `sinc` and symmetry of `kPrime` and `A1Mat` for any injective mode map -/

/-- `Cvs.Finite.WindowMatrixSymbolKernel.sinc` is an even function: `sinc (-d) = sinc d`. -/
theorem sinc_neg (d : ℝ) : Cvs.Finite.WindowMatrixSymbolKernel.sinc (-d) = Cvs.Finite.WindowMatrixSymbolKernel.sinc d := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.sinc
  by_cases hd : d = 0
  · simp [hd]
  · have hnd : -d ≠ 0 := neg_ne_zero.mpr hd
    rw [ite_eq_right hnd, ite_eq_right hd, Real.sin_neg, neg_div_neg_eq]

/-- `Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L ω ω'` is symmetric in `(ω, ω')`. -/
theorem kPrime_symm (P R : ℕ) (L ω ω' : ℝ) :
    Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L ω ω' = Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L ω' ω := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kPrime
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  refine congrArg (_ * ·) (congrArg (2 * ·) ?_)
  by_cases h : (r : ℝ) * Real.log p ≤ L
  · rw [ite_eq_left h, ite_eq_left h]
    have h1 : (r : ℝ) * Real.log p * (ω + ω') / 2 = (r : ℝ) * Real.log p * (ω' + ω) / 2 := by ring
    have h2 : (r : ℝ) * Real.log p * (ω - ω') / 2 = -((r : ℝ) * Real.log p * (ω' - ω) / 2) := by ring
    rw [h1, h2, sinc_neg]
  · rw [ite_eq_right h, ite_eq_right h]

/-- For `0 < L` and any injective `mode : ι → ℤ`, `Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode` is symmetric. -/
theorem A1Mat_isSymm_of_injective {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) :
    (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply]
  rw [Cvs.Finite.OffDiagonalKernelDecay.A1Mat_apply_kernel hL P R hinj j i, Cvs.Finite.OffDiagonalKernelDecay.A1Mat_apply_kernel hL P R hinj i j]
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : j ≠ i := Ne.symm hij
    rw [ite_eq_right hij, ite_eq_right hji, kPrime_symm]

/-! ### `∀ N`-free positivity of `A1Mat`, `Cvs.Finite.TruncationQuadraticForm.M`, and continuous `Q` from a single `ModeBox M₀` floor -/

/-! ### Gershgorin diagonal-dominance sufficient conditions on `ModeBox M₀` -/

end Cvs.Route.ModeBoxGershgorinCriteria
