import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenGramRungFloors
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.EvenSlotSpectralMinorant
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.HighModeStripExcessFloor
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxUnconditional
import Cvs.Route.PoleOrthPrimeSinReduction
import Cvs.Route.PoleOrthogonalSubspace
import Cvs.Route.RepresenterFreeCrossBounds
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.ArithmeticFloorAboveBand
import Cvs.WeilForm.DistantTailCoupling
import Cvs.WeilForm.PrimeDiagonalBulkSchur
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# Form-Dominated `weightedLeakage` Reduction on `ModeBox M₀` and Canonical Targets

Bridges `Cvs.WeilForm.DistantTailCoupling.weighted_low_high_lower` to `modeCutoffRung N M₀` and `ModeBox M₀`, and packages the
four canonical target propositions for `RiemannHypothesis`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxWeightedLeakage
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.ArithmeticFloorAboveBand
open Cvs.WeilForm.PrimeDiagonalBulkSchur
open Cvs.WeilForm.DistantTailCoupling
open Cvs.Route.L1FloorFromBulkD0
open Cvs.L2a.EvenSectorReflectionBound
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenSlotSpectralMinorant
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.RepresenterFreeCrossBounds
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.EvenGramRungFloors
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Finite.EvenGramSymmetryBridges
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.HighModePoleTailDecay
open Cvs.Route.HalfPoleMatrixModeBox
open Cvs.Route.PoleOrthogonalSubspace
open Cvs.Route.HighModeStripExcessFloor
open Cvs.Route.PrimeSinDividedDifference
open Cvs.Route.FejerPrimeCosineSymbol
open Cvs.Route.PoleOrthPrimeSinReduction
open Cvs.Route.ModeBoxFgenCoupling
open Cvs.Route.ModeBoxUnconditional

/-! ### Bridge between `modeCutoffRung N M₀` / `Bulk` and `Cvs.WeilForm.PrimeDiagonalBulkSchur.lowPart` / `Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart` -/

/-- Every `r ∈ modeCutoffRung N M₀` is fixed by `Cvs.WeilForm.PrimeDiagonalBulkSchur.lowPart (M₀ + 1) N`. -/
theorem lowPart_succ_eq_self_of_mem_modeCutoffRung {N M₀ : ℕ}
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.lowPart (M₀ + 1) N r = r := by
  funext i
  simp only [Cvs.WeilForm.PrimeDiagonalBulkSchur.lowPart]
  split_ifs with hi
  · rfl
  · have hnot : i ∉ modeCutoffSet N M₀ := by
      change ¬ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
      omega
    exact (Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hnot).symm

/-- Every `w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)` is fixed by
`Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart (M₀ + 1) N`. -/
theorem highPart_succ_eq_self_of_bulk_modeCutoffRung {N M₀ : ℕ}
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart (M₀ + 1) N w = w := by
  funext i
  simp only [Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart]
  split_ifs with hi
  · have hmem : i ∈ modeCutoffSet N M₀ := by
      change (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
      omega
    exact (Cvs.Route.HighModePoleTailDecay.apply_eq_zero_of_mem_modeCutoffSet hw hmem).symm
  · rfl

/-- Zero-padded inverse map from `ModeBox M₀ → ℝ` to `Cvs.Finite.SymmetricModeSet.Idx N → ℝ`. -/
def fromModeBox (N M₀ : ℕ) (η : ModeBox M₀ → ℝ) (i : Cvs.Finite.SymmetricModeSet.Idx N) : ℝ :=
  if hi : i ∈ modeCutoffSet N M₀ then η (idxToModeBox i hi) else 0

/-- On `r ∈ modeCutoffRung N M₀`, `fromModeBox N M₀ (toModeBox N M₀ r) = r`. -/
theorem fromModeBox_toModeBox_of_mem_modeCutoffRung {N M₀ : ℕ}
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀) :
    fromModeBox N M₀ (toModeBox N M₀ r) = r := by
  funext i
  dsimp [fromModeBox]
  split_ifs with hi
  · exact Cvs.Route.ModeBoxIsometricTransfer.toModeBox_idxToModeBox r hi
  · exact (Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hi).symm

/-- `fromModeBox N M₀ η` vanishes at every mode index with `(mode N i).natAbs > M₀`. -/
theorem fromModeBox_apply_eq_zero_of_gt (N M₀ : ℕ) (η : ModeBox M₀ → ℝ)
    (i : Cvs.Finite.SymmetricModeSet.Idx N) (hi : M₀ < (Cvs.Finite.SymmetricModeSet.mode N i).natAbs) :
    fromModeBox N M₀ η i = 0 := by
  have hnot : i ∉ modeCutoffSet N M₀ := by
    change ¬ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
    omega
  simp [fromModeBox, hnot]

/-- Euclidean norm contraction for `fromModeBox`:
`fromModeBox N M₀ η ⬝ᵥ fromModeBox N M₀ η ≤ η ⬝ᵥ η`. -/
theorem fromModeBox_dotProduct_self_le (N M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    fromModeBox N M₀ η ⬝ᵥ fromModeBox N M₀ η ≤ η ⬝ᵥ η := by
  have hsupp : ∀ i, i ∉ modeCutoffSet N M₀ → fromModeBox N M₀ η i = 0 := by
    intro i hi
    simp [fromModeBox, hi]
  rw [← Cvs.Route.ModeBoxIsometricTransfer.toModeBox_dotProduct_self N M₀ hsupp]
  refine Finset.sum_le_sum fun m _ => ?_
  have hval : toModeBox N M₀ (fromModeBox N M₀ η) m =
      ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i = m.1 then η m else 0 := by
    dsimp [toModeBox, fromModeBox]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hmode : Cvs.Finite.SymmetricModeSet.mode N i = m.1
    · have hi : i ∈ modeCutoffSet N M₀ := by
        rw [← Cvs.Route.ModeBoxIsometricTransfer.mem_Icc_iff_mem_modeCutoffSet, hmode]
        exact m.2
      have hidx : idxToModeBox i hi = m := Subtype.ext hmode
      simp [hmode, hi, hidx]
    · simp [hmode]
  rw [hval]
  by_cases hex : ∃ i : Cvs.Finite.SymmetricModeSet.Idx N, Cvs.Finite.SymmetricModeSet.mode N i = m.1
  · obtain ⟨i₀, hi₀⟩ := hex
    have hcongr : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i = m.1 then η m else 0) =
        ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if i = i₀ then η m else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← hi₀, (Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff]
    rw [hcongr, Finset.sum_ite_eq', if_pos (Finset.mem_univ i₀)]
  · push Not at hex
    have hzero : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i = m.1 then η m else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg (hex i)
    rw [hzero, mul_zero]
    exact mul_self_nonneg (η m)

/-! ### Form-dominated `weightedLeakage` lower bound on `modeCutoffRung` and `ModeBox` -/

/-- **Form-dominated low/high lower bound on `modeCutoffRung N M₀` via `Cvs.WeilForm.DistantTailCoupling.weightedLeakage`.** -/
theorem M_quad_add_ge_sub_weightedLeakage_modeCutoffRung
    {L T : ℝ} (hL : 0 < L) (hT : 2 ≤ T) {P R N M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ M₀ + 1)
    (hgap : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    {r w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀)
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) -
        Cvs.WeilForm.DistantTailCoupling.weightedLeakage (M₀ + 1) P R L 0 N r ≤
      (r + w) ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ (r + w)) := by
  have h := Cvs.WeilForm.DistantTailCoupling.weighted_low_high_lower (μ := 0) hL hT (M₀ + 1) P R N hK hgap r w hw.1
    (lowPart_succ_eq_self_of_mem_modeCutoffRung hr)
    (highPart_succ_eq_self_of_bulk_modeCutoffRung hw)
  linarith

/-- **Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` from `weightedLeakage ≤ r ⬝ᵥ (M *ᵥ r)` on `modeCutoffRung N M₀`.** -/
theorem M_even_nonneg_of_modeCutoffRung_weightedLeakage
    {L T : ℝ} (hL : 0 < L) (hT : 2 ≤ T) {P R N M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ M₀ + 1)
    (hgap : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (hleak : ∀ r ∈ modeCutoffRung N M₀,
      Cvs.WeilForm.DistantTailCoupling.weightedLeakage (M₀ + 1) P R L 0 N r ≤
        r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  intro ξ hξ
  obtain ⟨r, hr, w, hw, rfl⟩ :=
    Cvs.Route.EvenMatrixSlotPoleRestored.exists_dec (modeCutoffRung_le_evenModeSub N M₀) ξ hξ
  have h1 := M_quad_add_ge_sub_weightedLeakage_modeCutoffRung hL hT hK hgap hr hw
  have h2 := hleak r hr
  linarith

/-- **Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` from `weightedLeakage` domination on `ModeBox M₀`.** -/
theorem M_even_nonneg_of_modeBox_weightedLeakage
    {L T : ℝ} (hL : 0 < L) (hT : 2 ≤ T) {P R N M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ M₀ + 1)
    (hgap : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (hleak : ∀ η ∈ evenModeSub (negBox M₀),
      Cvs.WeilForm.DistantTailCoupling.weightedLeakage (M₀ + 1) P R L 0 N (fromModeBox N M₀ η) ≤
        η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η)) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  refine M_even_nonneg_of_modeCutoffRung_weightedLeakage hL hT hK hgap fun r hr => ?_
  have hsupp : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0 :=
    fun _ hi => Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hi
  have hev : toModeBox N M₀ r ∈ evenModeSub (negBox M₀) :=
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox_mem_evenModeSub N M₀ (modeCutoffRung_le_evenModeSub N M₀ hr)
  have h := hleak (toModeBox N M₀ r) hev
  rwa [fromModeBox_toModeBox_of_mem_modeCutoffRung hr,
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox_M_quad_eq P R N M₀ L hsupp] at h

/-- **Explicit separated-buffer bound on `weightedLeakage` for `fromModeBox N M₀ η`.** -/
theorem weightedLeakage_fromModeBox_buffer_le
    {L T ε : ℝ} (hL : 0 < L) (hT : 2 ≤ T) (hε : 0 < ε)
    (K P R N M₀ : ℕ) (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ K)
    (hbuffer : Cvs.WeilForm.DistantTailCoupling.bufferCutoff P R L M₀ (ε * Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T) ≤ K)
    (hgap : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (η : ModeBox M₀ → ℝ) :
    Cvs.WeilForm.DistantTailCoupling.weightedLeakage K P R L 0 N (fromModeBox N M₀ η) ≤ ε * (η ⬝ᵥ η) := by
  have hbuf : Cvs.WeilForm.DistantTailCoupling.bufferCutoff P R L M₀ (ε * (Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T - 0)) ≤ K := by
    simpa using hbuffer
  have h1 := Cvs.WeilForm.DistantTailCoupling.weightedLeakage_buffer_le (μ := 0) hL hT hε K P R N M₀ hK hbuf hgap
    (fromModeBox N M₀ η) (fromModeBox_apply_eq_zero_of_gt N M₀ η)
  exact h1.trans (mul_le_mul_of_nonneg_left (fromModeBox_dotProduct_self_le N M₀ η) hε.le)

/-- Continuous even window positivity `∀ v ∈ Ev x, 0 ≤ Qx x v` at `x ≥ 2` from `ModeBox M₀`
`weightedLeakage` domination. -/
theorem Qx_Ev_nonneg_of_modeBox_weightedLeakage {x : ℕ} (hx : 2 ≤ x)
    {T : ℝ} {M₀ : ℕ} (hT : 2 ≤ T)
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) T ≤ M₀ + 1)
    (hgap : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor x (Nat.clog 2 x) T)
    (hleak : ∀ N : ℕ, ∀ η ∈ evenModeSub (negBox M₀),
      Cvs.WeilForm.DistantTailCoupling.weightedLeakage (M₀ + 1) x (Nat.clog 2 x) (Real.log x) 0 N (fromModeBox N M₀ η)
        ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η)) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  exact (Cvs.Route.EvenMatrixSlotPoleRestored.Qx_Ev_nonneg_iff_M_even_nonneg hx).2
    (fun N => M_even_nonneg_of_modeBox_weightedLeakage hL hT hK hgap (hleak N))

/-! ### Four canonical target propositions and 1-hypothesis bridges to `RiemannHypothesis` -/

/-- **Target 1 (`ModeBoxWeightedLeakageTarget`)**: form-dominated `weightedLeakage` inequality on
`ModeBox M₀` at infinitely many integer scales `x : ℕ`. -/
def ModeBoxWeightedLeakageTarget : Prop :=
  ∃ᶠ x : ℕ in atTop,
    ∃ (T : ℝ) (M₀ : ℕ),
      2 ≤ T ∧
      Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) T ≤ M₀ + 1 ∧
      0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor x (Nat.clog 2 x) T ∧
      ∀ N : ℕ, ∀ η ∈ evenModeSub (negBox M₀),
        Cvs.WeilForm.DistantTailCoupling.weightedLeakage (M₀ + 1) x (Nat.clog 2 x) (Real.log x) 0 N
          (fromModeBox N M₀ η)
          ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η)

/-- `ModeBoxWeightedLeakageTarget` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_modeBoxWeightedLeakageTarget
    (h : ModeBoxWeightedLeakageTarget) : RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_)
  obtain ⟨T, M₀, hT, hK, hgap, hleak⟩ := hx
  exact Qx_Ev_nonneg_of_modeBox_weightedLeakage hx2 hT hK hgap hleak

/-- **Target 2 (`ModeBoxFloorTarget`)**: unconditional `∀ N`-free `ModeBox M₀` Euclidean floor of
`Cvs.Finite.TruncationQuadraticForm.M` at infinitely many integer scales `x : ℕ`. -/
def ModeBoxFloorTarget : Prop :=
  ∃ᶠ x : ℕ in atTop,
    ∃ (C cM : ℝ) (M₀ : ℕ),
      0 ≤ C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x) ∧
      0 ≤ cM ∧
      Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ) ∧
      (∀ η ∈ evenModeSub (negBox M₀),
        cM * (η ⬝ᵥ η)
          ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η)) ∧
      (Cvs.WeilForm.DistantTailCoupling.generatorBudget x (Nat.clog 2 x) (Real.log x) / π) ^ 2
          * (4 * (2 * (M₀ : ℝ) + 1))
        ≤ cM * (C - Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost x (Nat.clog 2 x))

/-- `ModeBoxFloorTarget` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_modeBoxFloorTarget
    (h : ModeBoxFloorTarget) : RiemannHypothesis :=
  Cvs.Route.ModeBoxUnconditional.riemannHypothesis_of_modeBox_M_floor_unconditional h

/-- **Target 3 (`PoleOrthSubA1Target`)**: `A1Mat`-only codimension-1 `poleOrthSub` floor with
`BulkStripExcess` and `IntModePrimeSinBound` at infinitely many integer scales `x : ℕ`. -/
def PoleOrthSubA1Target : Prop :=
  ∃ᶠ x : ℕ in atTop,
    ∃ (C B_strip B_sin cA cR δ : ℝ) (M₀ : ℕ),
      0 ≤ apoleBulkConstGen (Real.log x) C B_strip M₀ ∧
      0 ≤ cR ∧
      0 ≤ δ ∧
      cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor (Real.log x) / Real.log x ∧
      Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ) ∧
      (∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip) ∧
      IntModePrimeSinBound x (Nat.clog 2 x) (Real.log x) B_sin ∧
      (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
        ≤ cR * apoleBulkConstGen (Real.log x) C B_strip M₀ ∧
      (∀ ζ ∈ poleOrthSub (Real.log x) M₀,
        (cR + δ) * (ζ ⬝ᵥ ζ)
          ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ ζ)) ∧
      cA * (boxPoleVec (Real.log x) M₀ ⬝ᵥ boxPoleVec (Real.log x) M₀)
        ≤ boxPoleVec (Real.log x) M₀
          ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀)
            *ᵥ boxPoleVec (Real.log x) M₀) ∧
      ∀ ζ ∈ poleOrthSub (Real.log x) M₀,
        (boxPoleVec (Real.log x) M₀
            ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ ζ)) ^ 2
          ≤ (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor (Real.log x) / Real.log x - cR)
            * (boxPoleVec (Real.log x) M₀ ⬝ᵥ boxPoleVec (Real.log x) M₀) * (δ * (ζ ⬝ᵥ ζ))

/-- `PoleOrthSubA1Target` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_poleOrthSubA1Target
    (h : PoleOrthSubA1Target) : RiemannHypothesis :=
  Cvs.Route.PoleOrthPrimeSinReduction.riemannHypothesis_of_poleOrthSub_A1Mat_only h

/-- **Target 4 (`ProlateReflectionTarget`)**: representer-free spectral Gram cross-term bound against
`evenGram x` at infinitely many integer scales `x : ℕ`. -/
def ProlateReflectionTarget : Prop :=
  ∃ᶠ x : ℕ in atTop, ∃ (n : ℕ) (φ : Fin n → Cvs.Route.L1FloorFromBulkD0.Dom x) (g : Fin n → ℝ)
    (A : LinearMap.BilinForm ℝ (Cvs.Route.L1FloorFromBulkD0.Dom x)) (c : Cvs.Route.L1FloorFromBulkD0.Dom x → Fin n → ℝ)
    (B_rem : Cvs.Route.L1FloorFromBulkD0.Dom x → Cvs.Route.L1FloorFromBulkD0.Dom x → ℝ),
    (∀ k, 0 < g k) ∧ (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w) ∧
    Cvs.Route.EvenSlotSpectralMinorant.SpecComparison x φ g A ∧ Cvs.Route.RepresenterFreeCrossBounds.SpecRemRepresentation x φ c B_rem ∧
    SpecGramCrossBound x g A c B_rem

/-- `ProlateReflectionTarget` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_prolateReflectionTarget
    (h : ProlateReflectionTarget) : RiemannHypothesis :=
  Cvs.Route.EvenGramRungFloors.riemannHypothesis_of_specGram_crossBound h

end Cvs.Route.ModeBoxWeightedLeakage
