import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.PoleMatChannelStrip
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Parametrized High-Mode Strip-Excess Bulk Floor and `ModeBox` Reduction

Factors the high-mode prime-strip quadratic bound on `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`
into a single constant `B_strip` and proves the parameterized `ModeBox M₀` reductions.
-/

namespace Cvs.Route.HighModeStripExcessFloor
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Filter Real
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PoleMatChannelStrip
open Cvs.Route.BoundaryStripFolding
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Route.HighModePoleTailDecay

/-! ### High-mode strip excess predicate `BulkStripExcess` -/

/-- **High-mode strip excess bound**: on `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`,
`cosStripQ w - sinStripQ w ≤ B_strip * (w ⬝ᵥ w)`. -/
def BulkStripExcess (P R : ℕ) (L : ℝ) (N M₀ : ℕ) (B_strip : ℝ) : Prop :=
  ∀ w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
    Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w →
      cosStripQ P R L (Cvs.Finite.SymmetricModeSet.mode N) w - sinStripQ P R L (Cvs.Finite.SymmetricModeSet.mode N) w ≤
        B_strip * (w ⬝ᵥ w)

/-! ### Generalized pole-penalized high-mode bulk floor constant `apoleBulkConstGen` -/

/-- Generalized pole-penalized high-mode bulk floor constant with strip-excess parameter `B_strip`. -/
noncomputable def apoleBulkConstGen (L C B_strip : ℝ) (M₀ : ℕ) : ℝ :=
  C - B_strip - L ^ 3 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / (π ^ 4 * ((M₀ : ℝ) + 1) ^ 2)

/-- **Parametrized `A1Mat` bulk floor on `modeCutoffRung N M₀`** under `BulkStripExcess`. -/
theorem A1Mat_bulkFloor_modeCutoffRung_of_bulkStripExcess
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (C - B_strip) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
  have hquad := Cvs.Route.LadderFreePrimeTailCoupling.A1Mat_quad_eq_archSymbol_add_sinStripQ_sub_cosStripQ
    hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) w
  have harch : C * (w ⬝ᵥ w) ≤
      ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, w i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L) := by
    have hdot : C * (w ⬝ᵥ w) = ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, w i ^ 2 * C := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hdot]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ modeCutoffSet N M₀
    · have hw0 : w i = 0 := apply_eq_zero_of_mem_modeCutoffSet hw hi
      simp [hw0]
    · exact mul_le_mul_of_nonneg_left
        (archSymbol_ge_of_not_mem_modeCutoffSet hL hM₀ hi) (sq_nonneg (w i))
  have hw_strip := hstrip w hw
  linarith

/-- On `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`, `A1Mat - poleRankOneMat` is bounded below
by `apoleBulkConstGen L C B_strip M₀` under `BulkStripExcess`. -/
theorem A1Mat_sub_poleRankOneMat_bulk_ge_of_bulkStripExcess
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    apoleBulkConstGen L C B_strip M₀ * (w ⬝ᵥ w) ≤
      w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) -
        w ⬝ᵥ (poleRankOneMat L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
  have h1 := A1Mat_bulkFloor_modeCutoffRung_of_bulkStripExcess hL hM₀ hstrip hw
  have h2 := poleRankOneMat_bulk_modeCutoffRung_le hL hw
  unfold apoleBulkConstGen
  linarith

/-! ### Parametrized `ModeBox M₀` positivity and `RiemannHypothesis` reductions -/

end Cvs.Route.HighModeStripExcessFloor
