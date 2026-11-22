import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenBulkModeMatrices
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxEndpointFlatSchur
import Cvs.Route.ModeBoxGreenLaplace
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxLogMinorant
import Cvs.Route.ModeBoxPureCurvature
import Cvs.Route.ModeBoxRightInverse
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.Route.ModeBoxVolterraCurvature
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.PrimeMomentVolterra
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# Bulk-Projected Log-Retained Four-Channel Slot and Connes Rung Reduction

Packages the matrix slot for `Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant`, proves endpoint elimination on
bulk vectors orthogonal to `boxOnesVec M₀`, and bridges the minorant to `Cvs.Finite.EvenBulkModeMatrices.MatFloorN`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxLogSlotConnesRung
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
open Cvs.Finite.SymmetricModeSet
open Cvs.Upstream.MergedBoundSchurForm
open Cvs.WeilForm.PrimeMomentVolterra
open Cvs.Route.L1FloorFromBulkD0
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Finite.EvenBulkModeMatrices
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxRightInverse
open Cvs.Route.ModeBoxShiftedArchGreen
open Cvs.Route.ModeBoxEndpointFlatSchur
open Cvs.Route.ModeBoxVolterraCurvature
open Cvs.Route.ModeBoxFourChannelLevy
open Cvs.Route.ModeBoxGreenLaplace
open Cvs.Route.ModeBoxPureCurvature
open Cvs.Route.ModeBoxLogMinorant

/-! ### Symmetry of `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀` and the Log-Retained Four-Channel Slot -/

/-- `Cvs.Finite.TruncationQuadraticForm.M P R L mode` is symmetric for any index type `ι` and map `mode : ι → ℤ`. -/
theorem M_mode_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι] (P R : ℕ) (L : ℝ) (mode : ι → ℤ) :
    (Cvs.Finite.TruncationQuadraticForm.M P R L mode).IsSymm :=
  Cvs.Finite.DividedDifferenceCommutator.ddMatrix_isSymm

/-- **The log-retained four-channel matrix slot on `ModeBox M₀`**: a rung subspace
`Rg ≤ evenModeSub (negBox M₀)` and weight `κ` with bulk floor and coupling in
`boxFourChannelLogMinorant` geometry paid by `Cvs.Finite.TruncationQuadraticForm.M` on `Rg`. -/
def BoxFourChannelLogSlot (P R : ℕ) (L : ℝ) (M₀ : ℕ) : Prop :=
  ∃ (Rg : Submodule ℝ (ModeBox M₀ → ℝ)) (κ : (ModeBox M₀ → ℝ) → ℝ),
    Rg ≤ evenModeSub (negBox M₀) ∧
    (∀ w, Bulk (evenModeSub (negBox M₀)) Rg w →
      0 ≤ w ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ w)) ∧
    (∀ r ∈ Rg, ∀ w, Bulk (evenModeSub (negBox M₀)) Rg w →
      (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ w)) ^ 2 ≤
        κ r * (w ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ w))) ∧
    (∀ r ∈ Rg, 0 ≤ κ r ∧ κ r ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ r))

/-- **`BoxFourChannelLogSlot P R L M₀` implies even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀`.** -/
theorem boxM_even_nonneg_of_boxFourChannelLogSlot
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    (h : BoxFourChannelLogSlot P R L M₀) :
    ∀ η ∈ evenModeSub (negBox M₀), 0 ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η) := by
  obtain ⟨Rg, κ, hRE, hf, hc, hk⟩ := h
  exact Cvs.Route.EvenMatrixSlotPoleRestored.nonneg_of_slot (M_mode_isSymm P R L (boxMode M₀)) hRE hf
    (fun w hw => boxFourChannelLogMinorant_le_boxM hL P R M₀ hw.1) hc
    (fun r hr => (hk r hr).1) (fun r hr => (hk r hr).2)

/-- Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀` fills `BoxFourChannelLogSlot P R L M₀`. -/
theorem boxFourChannelLogSlot_of_boxM_even_nonneg
    (P R : ℕ) (L : ℝ) (M₀ : ℕ)
    (h : ∀ η ∈ evenModeSub (negBox M₀), 0 ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η)) :
    BoxFourChannelLogSlot P R L M₀ := by
  have hw0 : ∀ w, Bulk (evenModeSub (negBox M₀)) (evenModeSub (negBox M₀)) w → w = 0 :=
    fun w hw => dotProduct_self_eq_zero.1 (hw.2 w hw.1)
  refine ⟨evenModeSub (negBox M₀), fun _ => 0, le_rfl, fun w hw => ?_, fun r _ w hw => ?_,
    fun r hr => ⟨le_rfl, h r hr⟩⟩
  · rw [hw0 w hw]; simp
  · rw [hw0 w hw]; simp

/-- **Equivalence between even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀` and
`BoxFourChannelLogSlot P R L M₀`.** -/
theorem boxM_even_nonneg_iff_boxFourChannelLogSlot
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) :
    (∀ η ∈ evenModeSub (negBox M₀), 0 ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η)) ↔
      BoxFourChannelLogSlot P R L M₀ :=
  ⟨boxFourChannelLogSlot_of_boxM_even_nonneg P R L M₀,
    boxM_even_nonneg_of_boxFourChannelLogSlot hL P R M₀⟩

/-! ### Endpoint-Flat Bulk Reduction when `boxOnesVec M₀ ∈ Rg` or `boxZeroVec M₀ ∈ Rg` -/

/-- The all-ones vector on `ModeBox M₀`, dual to the endpoint functional `boxEndpoint M₀`. -/
def boxOnesVec (M₀ : ℕ) : ModeBox M₀ → ℝ :=
  fun _ => 1

/-- `boxOnesVec M₀` belongs to `evenModeSub (negBox M₀)`. -/
theorem boxOnesVec_mem_evenModeSub (M₀ : ℕ) :
    boxOnesVec M₀ ∈ evenModeSub (negBox M₀) :=
  fun _ => rfl

/-- Dot product with `boxOnesVec M₀` equals `boxEndpoint M₀ η`. -/
theorem boxOnesVec_dotProduct (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    boxOnesVec M₀ ⬝ᵥ η = boxEndpoint M₀ η := by
  simp [dotProduct, boxOnesVec, boxEndpoint]

/-- If `boxZeroVec M₀ ∈ Rg`, every bulk vector `w` against `Rg` vanishes at `zeroModeBox M₀`. -/
theorem apply_zeroModeBox_eq_zero_of_bulk_of_boxZeroVec_mem
    {M₀ : ℕ} {Rg : Submodule ℝ (ModeBox M₀ → ℝ)}
    (hz : boxZeroVec M₀ ∈ Rg) {w : ModeBox M₀ → ℝ}
    (hw : Bulk (evenModeSub (negBox M₀)) Rg w) :
    w (zeroModeBox M₀) = 0 := by
  rw [← boxZeroVec_dotProduct M₀ w]
  exact hw.2 (boxZeroVec M₀) hz

/-- If `boxOnesVec M₀ ∈ Rg`, every bulk vector `w` against `Rg` has `boxEndpoint M₀ w = 0`. -/
theorem boxEndpoint_eq_zero_of_bulk_of_boxOnesVec_mem
    {M₀ : ℕ} {Rg : Submodule ℝ (ModeBox M₀ → ℝ)}
    (h1 : boxOnesVec M₀ ∈ Rg) {w : ModeBox M₀ → ℝ}
    (hw : Bulk (evenModeSub (negBox M₀)) Rg w) :
    boxEndpoint M₀ w = 0 := by
  rw [← boxOnesVec_dotProduct M₀ w]
  exact hw.2 (boxOnesVec M₀) h1

/-- If `boxOnesVec M₀ ∈ Rg`, every bulk vector `w` against `Rg` belongs to `boxFlatSub M₀`. -/
theorem mem_boxFlatSub_of_bulk_of_boxOnesVec_mem
    {M₀ : ℕ} {Rg : Submodule ℝ (ModeBox M₀ → ℝ)}
    (h1 : boxOnesVec M₀ ∈ Rg) {w : ModeBox M₀ → ℝ}
    (hw : Bulk (evenModeSub (negBox M₀)) Rg w) :
    w ∈ boxFlatSub M₀ :=
  ⟨hw.1, boxEndpoint_eq_zero_of_bulk_of_boxOnesVec_mem h1 hw⟩

/-- **On `boxFlatSub M₀`, `boxFourChannelLogMinorant` reduces to `truncConst 4` plus `boxLogGainQ 4`
minus the three Green channels and `boxPureCurvatureMatrix`** (the endpoint ramp vanishes). -/
theorem boxFourChannelLogMinorant_quad_eq_pureCurvature_of_mem_boxFlatSub
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) {w : ModeBox M₀ → ℝ}
    (hw : w ∈ boxFlatSub M₀) :
    w ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ w) =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 * (w ⬝ᵥ w) + boxLogGainQ 4 L M₀ w -
        (∑ k ∈ Finset.Ico 1 4, w ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ w)) -
        w ⬝ᵥ (boxPureCurvatureMatrix L M₀
          (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ w) := by
  rw [boxFourChannelLogMinorant_quad_eq P R L M₀ w,
    boxDiscrepancyMatrix_quad_eq_endpoint_add_curvature P R L M₀ w,
    discrepancyEntry_zero_zero hL P R,
    boxCurvatureDiscrepancyMatrix_quad_eq_pureCurvature hL P R M₀ (Cvs.Route.ModeBoxEndpointFlatSchur.mem_boxFlatSub_iff.mp hw).1,
    (Cvs.Route.ModeBoxEndpointFlatSchur.mem_boxFlatSub_iff.mp hw).2, sq, mul_zero, mul_zero, zero_add]

/-- **When `boxOnesVec M₀ ∈ Rg`, `boxFourChannelLogMinorant` on the bulk reduces to pure curvature.** -/
theorem boxFourChannelLogMinorant_quad_eq_pureCurvature_of_bulk
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) {Rg : Submodule ℝ (ModeBox M₀ → ℝ)}
    (h1 : boxOnesVec M₀ ∈ Rg) {w : ModeBox M₀ → ℝ}
    (hw : Bulk (evenModeSub (negBox M₀)) Rg w) :
    w ⬝ᵥ (boxFourChannelLogMinorant P R L M₀ *ᵥ w) =
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 * (w ⬝ᵥ w) + boxLogGainQ 4 L M₀ w -
        (∑ k ∈ Finset.Ico 1 4, w ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ w)) -
        w ⬝ᵥ (boxPureCurvatureMatrix L M₀
          (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ w) :=
  boxFourChannelLogMinorant_quad_eq_pureCurvature_of_mem_boxFlatSub hL P R M₀
    (mem_boxFlatSub_of_bulk_of_boxOnesVec_mem h1 hw)

/-! ### Isometric Bridge from `ModeBox N` to `Idx N` and Connes' Rung Floor `Cvs.Finite.EvenBulkModeMatrices.MatFloorN` -/

/-- Every index `i : Cvs.Finite.SymmetricModeSet.Idx N` belongs to `modeCutoffSet N N`. -/
theorem mem_modeCutoffSet_self (N : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    i ∈ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N N := by
  change (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ N
  rcases i with _ | ⟨k, b⟩
  · simp [Cvs.Finite.SymmetricModeSet.mode]
  · cases b <;> simp [Cvs.Finite.SymmetricModeSet.mode] <;> omega

/-- At `M₀ = N`, `toModeBox N N` preserves the Euclidean norm of every `f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ`. -/
theorem toModeBox_self_dotProduct_self (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    toModeBox N N f ⬝ᵥ toModeBox N N f = f ⬝ᵥ f :=
  toModeBox_dotProduct_self N N fun i hi => False.elim (hi (mem_modeCutoffSet_self N i))

/-- At `M₀ = N`, `toModeBox N N` preserves the `Cvs.Finite.TruncationQuadraticForm.M` quadratic form of every `f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ`. -/
theorem toModeBox_self_M_quad_eq (P R N : ℕ) (L : ℝ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    toModeBox N N f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode N) *ᵥ toModeBox N N f) =
      f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ f) :=
  toModeBox_M_quad_eq P R N N L fun i hi => False.elim (hi (mem_modeCutoffSet_self N i))

/-- **For every even `f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ`, `boxFourChannelLogMinorant` on `toModeBox N N f` bounds
`f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f)` from below.** -/
theorem boxFourChannelLogMinorant_toModeBox_le_M_quad
    {L : ℝ} (hL : 0 < L) (P R N : ℕ) {f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hf : ∀ i, f (Cvs.Finite.SymmetricModeSet.negI N i) = f i) :
    toModeBox N N f ⬝ᵥ (boxFourChannelLogMinorant P R L N *ᵥ toModeBox N N f) ≤
      f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ f) := by
  rw [← toModeBox_self_M_quad_eq P R N L f]
  exact boxFourChannelLogMinorant_le_boxM hL P R N (toModeBox_mem_evenModeSub N N hf)

/-- **A `b`-floor of `boxFourChannelLogMinorant` on the `D₀`-orthogonal bulk (`rungNormal x N *ᵥ f = 0`)
implies `Cvs.Finite.EvenBulkModeMatrices.MatFloorN x N b`.** -/
theorem matFloorN_of_boxFourChannelLogMinorant_floor
    {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ) (b : ℝ)
    (hfloor : ∀ f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∀ i, f (Cvs.Finite.SymmetricModeSet.negI N i) = f i) →
      Cvs.Finite.EvenBulkModeMatrices.rungNormal x N *ᵥ f = 0 →
      b * (toModeBox N N f ⬝ᵥ toModeBox N N f) ≤
        toModeBox N N f ⬝ᵥ
          (boxFourChannelLogMinorant x (Nat.clog 2 x) (Real.log x) N *ᵥ toModeBox N N f)) :
    Cvs.Finite.EvenBulkModeMatrices.MatFloorN x N b := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  intro f hf hfD
  have h1 := hfloor f hf hfD
  rw [toModeBox_self_dotProduct_self N f] at h1
  exact h1.trans (boxFourChannelLogMinorant_toModeBox_le_M_quad hL x (Nat.clog 2 x) N hf)

/-- **A `b`-floor of `boxFourChannelLogMinorant` on the `D₀`-orthogonal bulk across all orders `N`
implies `Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b`.** -/
theorem bulkFloor_D0_of_boxFourChannelLogMinorant_floor
    {x : ℕ} (hx1 : (1 : ℝ) < x) (b : ℝ)
    (hfloor : ∀ N : ℕ, ∀ f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∀ i, f (Cvs.Finite.SymmetricModeSet.negI N i) = f i) →
      Cvs.Finite.EvenBulkModeMatrices.rungNormal x N *ᵥ f = 0 →
      b * (toModeBox N N f ⬝ᵥ toModeBox N N f) ≤
        toModeBox N N f ⬝ᵥ
          (boxFourChannelLogMinorant x (Nat.clog 2 x) (Real.log x) N *ᵥ toModeBox N N f)) :
    Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b :=
  (Cvs.Finite.EvenBulkModeMatrices.bulkFloor_iff_matFloor hx1 b).2 fun N =>
    matFloorN_of_boxFourChannelLogMinorant_floor hx1 N b (hfloor N)

/-- **`RiemannHypothesis` from a positive `boxFourChannelLogMinorant` floor on the `D₀`-orthogonal
bulk and `Cvs.Finite.EvenBulkModeMatrices.MatCoupling x δ` (`0 ≤ δ < 1`) at infinitely many scales `x`.** -/
theorem riemannHypothesis_of_boxFourChannelLogMinorant_floor_coupling
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      (∀ N : ℕ, ∀ f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
        (∀ i, f (Cvs.Finite.SymmetricModeSet.negI N i) = f i) →
        Cvs.Finite.EvenBulkModeMatrices.rungNormal x N *ᵥ f = 0 →
        b * (toModeBox N N f ⬝ᵥ toModeBox N N f) ≤
          toModeBox N N f ⬝ᵥ
            (boxFourChannelLogMinorant x (Nat.clog 2 x) (Real.log x) N *ᵥ toModeBox N N f)) ∧
      Cvs.Finite.EvenBulkModeMatrices.MatCoupling x δ) :
    RiemannHypothesis := by
  have hev : ∀ᶠ x : ℕ in atTop, (1 : ℝ) < x :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 1
  have hmat : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Finite.EvenBulkModeMatrices.MatFloor x b ∧ Cvs.Finite.EvenBulkModeMatrices.MatCoupling x δ :=
    (h.and_eventually hev).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hF, hC⟩, hx1⟩ =>
      ⟨b, δ, hb, hδ0, hδ1,
        fun N => matFloorN_of_boxFourChannelLogMinorant_floor hx1 N b (hF N), hC⟩
  exact (Cvs.Finite.EvenBulkModeMatrices.frequently_floor_coupling_D0_iff_rh_and_matFloor.1
    (Cvs.Finite.EvenBulkModeMatrices.frequently_floor_coupling_D0_iff_matrix.2 hmat)).1

end Cvs.Route.ModeBoxLogSlotConnesRung
