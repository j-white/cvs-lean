import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxFourChannelLevy
import Cvs.Route.ModeBoxGreenLaplace
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelBandSpectralGain
import Cvs.WeilForm.ChannelModeSumEnclosure
import Cvs.Zeta.Digamma

/-!
# Euler-Maclaurin Logarithmic Enclosure of `multiShiftedArchSymbol` and Log-Retained Minorant

Connects `Cvs.Route.ModeBoxFourChannelLevy.multiShiftedArchSymbol` to `Cvs.WeilForm.ChannelModeSumEnclosure.modeTail` and `Cvs.WeilForm.ChannelModeSumEnclosure.phi`, proving the closed-form
logarithmic lower bound `truncConst N + phi t (N + 1/4) ≤ multiShiftedArchSymbol N t` on `ModeBox M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxLogMinorant
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
open Cvs.WeilForm.Archimedean.TruncationBelowSymbol
open Cvs.WeilForm.ChannelBandSpectralGain
open Cvs.WeilForm.ChannelModeSumEnclosure
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxShiftedArchGreen
open Cvs.Route.ModeBoxFourChannelLevy
open Cvs.Route.ModeBoxGreenLaplace

/-! ### Bridge between `Cvs.WeilForm.ChannelBandSpectralGain.chanWeight`, `Cvs.WeilForm.ChannelModeSumEnclosure.modeTail`, and `Cvs.Zeta.digammaDeficit` -/

/-- The `k`-th Lévy channel weight `Cvs.WeilForm.ChannelBandSpectralGain.chanWeight (k + 1/4) t` equals `Cvs.Zeta.digammaDeficit t k`. -/
theorem chanWeight_add_quarter_eq_digammaDeficit (k : ℕ) (t : ℝ) :
    Cvs.WeilForm.ChannelBandSpectralGain.chanWeight ((k : ℝ) + 1 / 4) t = Cvs.Zeta.digammaDeficit t k := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 / 4 := by positivity
  rw [Cvs.WeilForm.ChannelBandSpectralGain.chanWeight_eq hk, Cvs.Zeta.digammaDeficit_eq]
  have h1 : (k : ℝ) + 1 / 4 = 1 / 4 + (k : ℝ) := by ring
  rw [h1]

/-- The shifted channel tail `Cvs.WeilForm.ChannelModeSumEnclosure.modeTail t (N + 1/4)` equals the shifted digamma-deficit series. -/
theorem modeTail_add_quarter_eq_tsum_digammaDeficit (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.ChannelModeSumEnclosure.modeTail t ((N : ℝ) + 1 / 4) = ∑' k : ℕ, Cvs.Zeta.digammaDeficit t (k + N) := by
  unfold Cvs.WeilForm.ChannelModeSumEnclosure.modeTail
  refine tsum_congr fun k => ?_
  have hshift : (N : ℝ) + 1 / 4 + (k : ℝ) = ((k + N : ℕ) : ℝ) + 1 / 4 := by
    push_cast
    ring
  rw [hshift, chanWeight_add_quarter_eq_digammaDeficit (k + N) t]

/-- Exact representation of `multiShiftedArchSymbol N t` as `truncConst N + modeTail t (N + 1/4)`. -/
theorem multiShiftedArchSymbol_eq_truncConst_add_modeTail (N : ℕ) (t : ℝ) :
    multiShiftedArchSymbol N t = Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N + Cvs.WeilForm.ChannelModeSumEnclosure.modeTail t ((N : ℝ) + 1 / 4) := by
  rw [multiShiftedArchSymbol_eq_truncConst_add_tsum N t,
    modeTail_add_quarter_eq_tsum_digammaDeficit N t]

/-! ### Closed-form Euler-Maclaurin logarithmic minorant `multiShiftedLogSymbol` -/

/-- Closed-form Euler-Maclaurin logarithmic minorant of `multiShiftedArchSymbol N`. -/
def multiShiftedLogSymbol (N : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N + Cvs.WeilForm.ChannelModeSumEnclosure.phi t ((N : ℝ) + 1 / 4)

/-- **Euler-Maclaurin logarithmic lower bound on `multiShiftedArchSymbol N t`**. -/
theorem multiShiftedLogSymbol_le_multiShiftedArchSymbol (N : ℕ) (t : ℝ) :
    multiShiftedLogSymbol N t ≤ multiShiftedArchSymbol N t := by
  rw [multiShiftedLogSymbol, multiShiftedArchSymbol_eq_truncConst_add_modeTail N t]
  have hN : (0 : ℝ) < (N : ℝ) + 1 / 4 := by positivity
  linarith [(Cvs.WeilForm.ChannelModeSumEnclosure.tail_enclosure hN t).1]

/-! ### Lifting `multiShiftedLogSymbol` and `boxLogGainQ` to `ModeBox M₀` -/

/-- Diagonal matrix of `multiShiftedLogSymbol N` on `ModeBox M₀`. -/
def boxMultiShiftedLogDiag (N : ℕ) (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  Matrix.diagonal (fun m : ModeBox M₀ =>
    multiShiftedLogSymbol N (2 * π * (boxMode M₀ m : ℝ) / L))

/-- Logarithmic frequency-gain quadratic form `∑_m phi(ω_m, N + 1/4) η_m²` on `ModeBox M₀`. -/
def boxLogGainQ (N : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : ModeBox M₀,
    Cvs.WeilForm.ChannelModeSumEnclosure.phi (2 * π * (boxMode M₀ m : ℝ) / L) ((N : ℝ) + 1 / 4) * (η m) ^ 2

/-- Exact decomposition of `boxMultiShiftedLogDiag N` into `truncConst N` plus `boxLogGainQ N`. -/
theorem boxMultiShiftedLogDiag_quad_eq_truncConst_add_logGain
    (N : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxMultiShiftedLogDiag N L M₀ *ᵥ η) =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N * (η ⬝ᵥ η) + boxLogGainQ N L M₀ η := by
  simp only [dotProduct, Matrix.mulVec_diagonal, boxMultiShiftedLogDiag,
    multiShiftedLogSymbol, boxLogGainQ, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => by ring

/-- Quadratic comparison `boxMultiShiftedLogDiag N ≤ boxMultiShiftedDiag N` on `ModeBox M₀`. -/
theorem boxMultiShiftedLogDiag_quad_le_boxMultiShiftedDiag
    (N : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxMultiShiftedLogDiag N L M₀ *ᵥ η) ≤
      η ⬝ᵥ (boxMultiShiftedDiag N L M₀ *ᵥ η) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, boxMultiShiftedLogDiag, boxMultiShiftedDiag]
  refine Finset.sum_le_sum fun m _ => ?_
  have h := mul_le_mul_of_nonneg_right
    (multiShiftedLogSymbol_le_multiShiftedArchSymbol N (2 * π * (boxMode M₀ m : ℝ) / L))
    (mul_self_nonneg (η m))
  linarith

/-! ### Log-retained four-channel minorant `boxFourChannelLogMinorant` on `ModeBox M₀` -/

/-- The log-retained four-channel minorant matrix on `ModeBox M₀`:
retains `boxMultiShiftedLogDiag 4` against the three Green channels `k = 1, 2, 3` and discrepancy. -/
def boxFourChannelLogMinorant (P R : ℕ) (L : ℝ) (M₀ : ℕ) :
    Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun i j =>
    boxMultiShiftedLogDiag 4 L M₀ i j -
      (∑ k ∈ Finset.Ico 1 4, boxGreenChannelMatrix L k M₀ i j) -
      boxDiscrepancyMatrix P R L M₀ i j

/-- Explicit quadratic-form expansion of `boxFourChannelLogMinorant`. -/
theorem boxFourChannelLogMinorant_quad_eq
    (P R : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ η) =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 * (η ⬝ᵥ η) + boxLogGainQ 4 L M₀ η -
        (∑ k ∈ Finset.Ico 1 4, η ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ η)) -
        η ⬝ᵥ (boxDiscrepancyMatrix P R L M₀ *ᵥ η) := by
  have hcomm : (∑ k ∈ Finset.Ico 1 4, η ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ η)) =
      ∑ i : ModeBox M₀, ∑ j : ModeBox M₀,
        η i * ((∑ k ∈ Finset.Ico 1 4, boxGreenChannelMatrix L k M₀ i j) * η j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [← boxMultiShiftedLogDiag_quad_eq_truncConst_add_logGain 4 L M₀ η, hcomm]
  simp only [dotProduct, Matrix.mulVec, boxFourChannelLogMinorant, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **On `evenModeSub (negBox M₀)`, `boxFourChannelLogMinorant` bounds `Cvs.Finite.TruncationQuadraticForm.M` from below.** -/
theorem boxFourChannelLogMinorant_le_boxM
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) {η : ModeBox M₀ → ℝ}
    (hη : η ∈ evenModeSub (negBox M₀)) :
    η ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ η) ≤
      η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η) := by
  rw [boxFourChannelLogMinorant_quad_eq P R L M₀ η,
    ← boxMultiShiftedLogDiag_quad_eq_truncConst_add_logGain 4 L M₀ η,
    boxM_quad_eq_multi_four_add_tailFrom_sub_green_sub_discrepancy hL P R M₀ η]
  have hdiag := boxMultiShiftedLogDiag_quad_le_boxMultiShiftedDiag 4 L M₀ η
  have htail := boxTailMatrixFrom_quad_nonneg hL 4 M₀ hη
  linarith

end Cvs.Route.ModeBoxLogMinorant
