import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxFgenCoupling
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.OddAboveDisplacement
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.DistantTailCoupling
import Cvs.WeilForm.PrimeDiagonalBulkSchur
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# Unconditional `∀ N`-Free `ModeBox M₀` Reduction for `Cvs.Finite.TruncationQuadraticForm.M`

Discharges `IntModeFgenBound` via `Cvs.WeilForm.DistantTailCoupling.generatorBudget` and the high-mode bulk floor of `Cvs.Finite.TruncationQuadraticForm.M`
via `Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost` and `Cvs.WeilForm.DistantTailCoupling.shiftedDiagonal_energy_le`, eliminating `∀ N : ℕ` completely.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxUnconditional
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.WeilForm.PrimeDiagonalBulkSchur
open Cvs.WeilForm.DistantTailCoupling
open Cvs.L2a.EvenSectorReflectionBound
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.RepresenterFreeCrossBounds
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree
open Cvs.Route.EvenGramRungFloors
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Finite.OffDiagonalKernelDecay
open Cvs.Finite.EvenGramSymmetryBridges
open Cvs.Route.PrimeMatHilbertSchmidtTail
open Cvs.Route.ModeSepSumUniformBound
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.HighModePoleTailDecay
open Cvs.Route.HighModeStripExcessFloor
open Cvs.Route.ModeBoxFgenCoupling

/-! ### Unconditional `IntModeFgenBound` via `Cvs.WeilForm.DistantTailCoupling.generatorBudget` -/

/-- At every integer mode frequency `2πm/L`, `|Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2πm/L)| ≤ generatorBudget P R L`. -/
theorem abs_Fgen_mode_le_generatorBudget {L : ℝ} (hL : 0 < L) (P R : ℕ) (m : ℤ) :
    |Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * (m : ℝ) / L)| ≤ Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L := by
  rw [← Cvs.Finite.WindowMatrixSymbolKernel.gen_eq_Fgen P R hL m]
  exact Cvs.WeilForm.DistantTailCoupling.abs_gen_le hL P R m

/-- **Unconditional `IntModeFgenBound`** with constant `Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L`. -/
theorem intModeFgenBound_generatorBudget {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    IntModeFgenBound P R L (Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L) :=
  fun m => abs_Fgen_mode_le_generatorBudget hL P R m

/-- **Unconditional cross-term bound for `Cvs.Finite.TruncationQuadraticForm.M`** between `modeCutoffRung N M₀` and its bulk. -/
theorem M_cross_sq_modeCutoffRung_le_generatorBudget
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    {r w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀)
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) ^ 2
      ≤ (Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) :=
  M_cross_sq_modeCutoffRung_le_of_intModeFgenBound
    hL (intModeFgenBound_generatorBudget hL P R) hr hw

/-! ### Unconditional high-mode bulk floor of `Cvs.Finite.TruncationQuadraticForm.M` on `modeCutoffRung N M₀` -/

/-- **Unconditional high-mode bulk floor of `Cvs.Finite.TruncationQuadraticForm.M`**: on `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`,
`(C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)`. -/
theorem M_bulk_ge_sub_primeCost
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
  have henergy := Cvs.WeilForm.DistantTailCoupling.shiftedDiagonal_energy_le (μ := 0) hL P R N w hw.1
  have hsum : (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w) ≤
      ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, Cvs.WeilForm.DistantTailCoupling.shiftedDiagonal P R L 0 N i * w i ^ 2 := by
    have hdot : (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w) =
        ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * w i ^ 2 := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hdot]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ modeCutoffSet N M₀
    · have hw0 : w i = 0 := apply_eq_zero_of_mem_modeCutoffSet hw hi
      simp [hw0]
    · have harch := archSymbol_ge_of_not_mem_modeCutoffSet hL hM₀ hi
      have hdiag : C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R ≤ Cvs.WeilForm.DistantTailCoupling.shiftedDiagonal P R L 0 N i := by
        unfold Cvs.WeilForm.DistantTailCoupling.shiftedDiagonal
        linarith
      exact mul_le_mul_of_nonneg_right hdiag (sq_nonneg (w i))
  linarith

/-! ### Unconditional `∀ N`-free reductions from `ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M` -/

/-- **Unconditional even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M`** from a `modeCutoffRung N M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`. -/
theorem M_even_nonneg_of_modeCutoffRung_M_floor_unconditional
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C cM : ℝ}
    (hb : 0 ≤ C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) (hcM : 0 ≤ cM)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hrung : ∀ r ∈ modeCutoffRung N M₀,
      cM * (r ⬝ᵥ r) ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r))
    (hsep : (Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R)) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  intro ξ hξ
  obtain ⟨r, hr, w, hw, rfl⟩ :=
    Cvs.Route.EvenMatrixSlotPoleRestored.exists_dec (modeCutoffRung_le_evenModeSub N M₀) ξ hξ
  have hsym : w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
      = r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (Cvs.StepA.OddAboveDisplacement.M_isSymm hL P R N).eq, dotProduct_comm]
  have hexp : (r + w) ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ (r + w))
      = r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
        + 2 * (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w))
        + w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hsym]
    ring
  have hr_floor : cM * (r ⬝ᵥ r) ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := hrung r hr
  have hw_floor := M_bulk_ge_sub_primeCost (P := P) (R := R) hL hM₀ hw
  have hrr : 0 ≤ r ⬝ᵥ r := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r
  have hww : 0 ≤ w ⬝ᵥ w := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg w
  have hA : 0 ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) :=
    le_trans (mul_nonneg hcM hrr) hr_floor
  have hW : 0 ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
    le_trans (mul_nonneg hb hww) hw_floor
  have hcross := M_cross_sq_modeCutoffRung_le_generatorBudget (P := P) (R := R) hL hr hw
  have hprod1 :
      (Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) ≤
        (cM * (r ⬝ᵥ r)) * ((C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w)) := by
    have hmul := mul_le_mul_of_nonneg_right hsep (mul_nonneg hrr hww)
    linarith
  have hprod2 :
      (cM * (r ⬝ᵥ r)) * ((C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) * (w ⬝ᵥ w)) ≤
        (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)) *
          (w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) :=
    mul_le_mul hr_floor hw_floor (mul_nonneg hb hww) hA
  have hquad := Cvs.Route.PoleSlotRungResidual.quad_nonneg_of_sq_le hA hW (le_trans hcross (le_trans hprod1 hprod2))
  linarith

/-- **Unconditional even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)` for all `N : ℕ`** from a single
`ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`. -/
theorem M_even_nonneg_of_modeBox_M_floor_unconditional
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {M₀ : ℕ} {C cM : ℝ}
    (hb : 0 ≤ C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R) (hcM : 0 ≤ cM)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η) ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η))
    (hsep : (Cvs.WeilForm.DistantTailCoupling.generatorBudget P R L / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R))
    (N : ℕ) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) :=
  M_even_nonneg_of_modeCutoffRung_M_floor_unconditional hL hb hcM hM₀
    (modeCutoffRung_M_floor_of_modeBox P R N M₀ L cM hrung) hsep

/-- **Unconditional continuous even window positivity `∀ v ∈ Ev x, 0 ≤ Qx x v` at `x ≥ 2`** from a
single `ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`. -/
theorem Qx_Ev_nonneg_of_modeBox_M_floor_unconditional {x : ℕ} (hx : 2 ≤ x)
    {C cM : ℝ} {M₀ : ℕ}
    (hb : 0 ≤ C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x)) (hcM : 0 ≤ cM)
    (hM₀ : Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η)
        ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η))
    (hsep : (Cvs.WeilForm.DistantTailCoupling.generatorBudget x (Nat.clog 2 x) (Real.log x) / π) ^ 2
        * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x))) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  exact (Cvs.Route.EvenMatrixSlotPoleRestored.Qx_Ev_nonneg_iff_M_even_nonneg hx).2
    (M_even_nonneg_of_modeBox_M_floor_unconditional hL hb hcM hM₀ hrung hsep)

/-- **Master unconditional `∀ N`-free `ModeBox M₀` reduction for `RiemannHypothesis`**:
reduces `RiemannHypothesis` to a single `(2M₀ + 1) × (2M₀ + 1)` floor of `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀`. -/
theorem riemannHypothesis_of_modeBox_M_floor_unconditional
    (h : ∃ᶠ x : ℕ in atTop,
      ∃ (C cM : ℝ) (M₀ : ℕ),
        0 ≤ C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x) ∧
        0 ≤ cM ∧
        Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ) ∧
        (∀ η ∈ evenModeSub (negBox M₀),
          cM * (η ⬝ᵥ η)
            ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η)) ∧
        (Cvs.WeilForm.DistantTailCoupling.generatorBudget x (Nat.clog 2 x) (Real.log x) / π) ^ 2
            * (4 * (2 * (M₀ : ℝ) + 1))
          ≤ cM * (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x))) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_)
  obtain ⟨C, cM, M₀, hb, hcM, hM₀, hrung, hsep⟩ := hx
  exact Qx_Ev_nonneg_of_modeBox_M_floor_unconditional hx2 hb hcM hM₀ hrung hsep

end Cvs.Route.ModeBoxUnconditional
