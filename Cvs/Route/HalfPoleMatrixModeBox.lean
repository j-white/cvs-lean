import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.ModeBoxGershgorinCriteria
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.PosChannelFloorCoercivity

/-!
# Half-Pole Matrix `ApoleHalfMat`, Pole-Cross-Free Decomposition, and `ModeBox` Transfer

Introduces `ApoleHalfMat = A1Mat + (1/2) • poleRankOneMat`, proves the pole-cross-free quadratic
lower bound on `ApoleMat`, and transfers `ModeBox M₀` floors of `ApoleHalfMat` to `lowModeRung`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.HalfPoleMatrixModeBox
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxGershgorinCriteria

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The half-pole matrix `ApoleHalfMat`, symmetry, and quadratic completion inequalities -/

omit [Fintype ι] in
/-- **The half-pole finite matrix** `ApoleHalfMat = A1Mat + (1 / 2) • poleRankOneMat`:
retains half of the rank-one pole boost while allowing the pole cross-term to be absorbed. -/
def ApoleHalfMat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode + (1 / 2 : ℝ) • Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode

omit [Fintype ι] [DecidableEq ι] in
/-- Elementary Young inequality `(1 / 2) * A² − B² ≤ (A + B)²`. -/
theorem add_sq_ge_half_sq_sub_sq (A B : ℝ) : 1 / 2 * A ^ 2 - B ^ 2 ≤ (A + B) ^ 2 := by
  nlinarith [sq_nonneg (A + 2 * B)]

omit [Fintype ι] [DecidableEq ι] in
/-- `Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode` is symmetric for any `L : ℝ` and `mode : ι → ℤ`. -/
theorem poleRankOneMat_isSymm (L : ℝ) (mode : ι → ℤ) :
    (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat]
  ring

/-- For `0 < L` and any injective `mode : ι → ℤ`, `ApoleHalfMat P R L mode` is symmetric. -/
theorem ApoleHalfMat_isSymm_of_injective {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) :
    (ApoleHalfMat P R L mode).IsSymm := by
  ext i j
  simp only [ApoleHalfMat, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    (Cvs.Route.ModeBoxGershgorinCriteria.A1Mat_isSymm_of_injective hL P R hinj).apply, (poleRankOneMat_isSymm L mode).apply]

/-- For `0 < L`, `ApoleHalfMat P R L (boxMode M₀)` on `ModeBox M₀` is symmetric. -/
theorem ApoleHalfMat_boxMode_isSymm {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) :
    (ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀)).IsSymm :=
  ApoleHalfMat_isSymm_of_injective hL P R (Cvs.Route.ModeBoxIsometricTransfer.boxMode_injective M₀)

/-! ### Pole-cross-free quadratic decomposition of `poleRankOneMat` and `ApoleMat` -/

omit [DecidableEq ι] in
/-- The quadratic form of `poleRankOneMat` is the single square `(2 poleFactor L / L) * (∑_i ξ_i uu(1/2, ω_i))²`. -/
theorem poleRankOneMat_quad_eq (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ ξ)
      = (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
        * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat, Finset.mul_sum, sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of `ApoleHalfMat` is `A1Mat` plus `1 / 2` times `poleRankOneMat`. -/
theorem ApoleHalfMat_quad_eq (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (ApoleHalfMat P R L mode *ᵥ ξ)
      = ξ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ ξ)
        + 1 / 2 * (ξ ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ ξ)) := by
  simp [ApoleHalfMat, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]

omit [DecidableEq ι] in
/-- **Pole-cross-free quadratic lower bound for `poleRankOneMat`**:
for `0 < L`, `(1 / 2) * rᵀ poleRankOneMat r − wᵀ poleRankOneMat w ≤ (r + w)ᵀ poleRankOneMat (r + w)`. -/
theorem poleRankOneMat_add_quad_ge_half {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (r w : ι → ℝ) :
    1 / 2 * (r ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ r))
      - w ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ w)
      ≤ (r + w) ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ (r + w)) := by
  rw [poleRankOneMat_quad_eq L mode r, poleRankOneMat_quad_eq L mode w,
    poleRankOneMat_quad_eq L mode (r + w)]
  have hsum : (∑ i, (r + w) i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L))
      = (∑ i, r i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L))
        + (∑ i, w i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.add_apply, add_mul]
  rw [hsum]
  have hc : 0 ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L := by
    have := Cvs.Route.PosChannelFloorCoercivity.poleFactor_nonneg L
    positivity
  have hsq := add_sq_ge_half_sq_sub_sq
    (∑ i, r i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L))
    (∑ i, w i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L))
  have hmul := mul_le_mul_of_nonneg_left hsq hc
  linarith

/-- **Pole-cross-free quadratic lower bound for `ApoleMat`**:
retains `rᵀ ApoleHalfMat r` on `r`, has cross-term `2 rᵀ A1Mat w` (purely `A1Mat`, no pole cross-coupling),
and bulk term `wᵀ A1Mat w − wᵀ poleRankOneMat w`. -/
theorem ApoleMat_add_quad_ge_ApoleHalfMat {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) (r w : ι → ℝ) :
    r ⬝ᵥ (ApoleHalfMat P R L mode *ᵥ r)
      + 2 * (r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ w))
      + (w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ w) - w ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L mode *ᵥ w))
      ≤ (r + w) ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.ApoleMat P R L mode *ᵥ (r + w)) := by
  rw [Cvs.Route.LadderFreePrimeTailCoupling.ApoleMat_eq_A1Mat_add_poleRankOneMat P R L mode,
    Matrix.add_mulVec, dotProduct_add, ApoleHalfMat_quad_eq]
  have hsym : w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ r) = r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (Cvs.Route.ModeBoxGershgorinCriteria.A1Mat_isSymm_of_injective hL P R hinj).eq, dotProduct_comm]
  have hA1 : (r + w) ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ (r + w))
      = r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ r)
        + 2 * (r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ w))
        + w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ w) := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hsym]
    ring
  linarith [poleRankOneMat_add_quad_ge_half hL mode r w]

/-! ### Isometric preservation of `poleRankOneMat` and `ApoleHalfMat` under `toModeBox` -/

/-- Integer-mode kernel of `Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L`. -/
def modeKernelPole (L : ℝ) (m₁ m₂ : ℤ) : ℝ :=
  (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
    * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * m₁ / L) * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * m₂ / L)

/-- **`toModeBox` preserves the `poleRankOneMat` quadratic form** for `r` supported on `modeCutoffSet N M₀`. -/
theorem toModeBox_poleRankOneMat_quad (L : ℝ) {N M₀ : ℕ} {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀, r i = 0) :
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r)
      = r ⬝ᵥ (Cvs.Route.LadderFreePrimeTailCoupling.poleRankOneMat L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) :=
  Cvs.Route.ModeBoxIsometricTransfer.toModeBox_quad_eq N M₀ (modeKernelPole L) hr

/-- **`toModeBox` preserves the `ApoleHalfMat` quadratic form** for `r` supported on `modeCutoffSet N M₀`. -/
theorem toModeBox_ApoleHalfMat_quad (P R : ℕ) (L : ℝ) {N M₀ : ℕ} {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀, r i = 0) :
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r)
      = r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := by
  rw [ApoleHalfMat_quad_eq, ApoleHalfMat_quad_eq,
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox_A1Mat_quad_eq P R N M₀ L hr, toModeBox_poleRankOneMat_quad L hr]

/-- **Transfer of an `N`-independent `ApoleHalfMat` floor on `ModeBox M₀` to `modeCutoffRung N M₀` for all `N`.** -/
theorem modeCutoffRung_ApoleHalfMat_floor_of_modeBox {P R : ℕ} {L cR : ℝ} {M₀ : ℕ}
    (hfloor : ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
      cR * (η ⬝ᵥ η) ≤ η ⬝ᵥ (ApoleHalfMat P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η))
    (N : ℕ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ Cvs.Route.FreqThresholdModeCutoff.modeCutoffRung N M₀) :
    cR * (r ⬝ᵥ r) ≤ r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := by
  have hsupp : ∀ i, i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀ → r i = 0 :=
    fun _ hi => Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hi
  have hev : Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀) :=
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox_mem_evenModeSub N M₀ (Cvs.Route.FreqThresholdModeCutoff.modeCutoffRung_le_evenModeSub N M₀ hr)
  have h := hfloor (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r) hev
  rwa [Cvs.Route.ModeBoxIsometricTransfer.toModeBox_dotProduct_self N M₀ hsupp, toModeBox_ApoleHalfMat_quad P R L hsupp] at h

end Cvs.Route.HalfPoleMatrixModeBox
