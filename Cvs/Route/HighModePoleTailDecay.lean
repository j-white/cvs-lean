import Mathlib
import Cvs.Finite.OffDiagonalKernelDecay
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModeTailArchFree
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.ModeSepSumUniformBound
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# High-Mode Pole-Tail Decay and `modeCutoffRung` Bulk and Cross-Term Bounds

Proves the `(M₀ + 1)⁻²` high-mode decay of `poleRankOneMat` outside `modeCutoffSet N M₀` together
with the `A1Mat` bulk floor and `A1Mat` cross-term bound on `modeCutoffRung N M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.HighModePoleTailDecay
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PoleMatDefiniteSign
open Cvs.Route.PoleMatChannelStrip
open Cvs.Route.BoundaryStripFolding
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Finite.OffDiagonalKernelDecay
open Cvs.Route.PrimeMatHilbertSchmidtTail
open Cvs.Route.ModeSepSumUniformBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Decidability instance for membership in `modeCutoffSet N M₀`. -/
instance instDecidablePredMemModeCutoffSet (N M₀ : ℕ) :
    DecidablePred (· ∈ modeCutoffSet N M₀) :=
  fun i => Nat.decLe (Cvs.Finite.SymmetricModeSet.mode N i).natAbs M₀

/-! ### Rank-one pole vector `poleVec` and `poleRankOneMat` quadratic form -/

/-- **The pole evaluation vector** `poleVec L mode i = uu(1/2, 2π mode(i) / L)`. -/
def poleVec (L : ℝ) (mode : ι → ℤ) : ι → ℝ :=
  fun i => Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)

omit [Fintype ι] [DecidableEq ι] in
/-- `poleVec L mode i` is strictly positive for all `i`. -/
theorem poleVec_pos (L : ℝ) (mode : ι → ℤ) (i : ι) :
    0 < poleVec L mode i :=
  Cvs.Route.PosChannelFloorCoercivity.uu_pos (by norm_num) _

omit [Fintype ι] [DecidableEq ι] in
/-- `poleVec L mode i` is nonnegative for all `i`. -/
theorem poleVec_nonneg (L : ℝ) (mode : ι → ℤ) (i : ι) :
    0 ≤ poleVec L mode i :=
  (poleVec_pos L mode i).le

omit [DecidableEq ι] in
/-- Action of `poleRankOneMat L mode` on a vector `ξ`:
`(poleRankOneMat L mode *ᵥ ξ) i = (2 * poleFactor L / L) * poleVec L mode i * (poleVec L mode ⬝ᵥ ξ)`. -/
theorem poleRankOneMat_mulVec (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) (i : ι) :
    (poleRankOneMat L mode *ᵥ ξ) i
      = (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * poleVec L mode i * (poleVec L mode ⬝ᵥ ξ) := by
  simp only [Matrix.mulVec, dotProduct, poleRankOneMat, poleVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- Quadratic form of `poleRankOneMat L mode`:
`ξ ⬝ᵥ (poleRankOneMat L mode *ᵥ ξ) = (2 * poleFactor L / L) * (poleVec L mode ⬝ᵥ ξ)²`. -/
theorem poleRankOneMat_quad_eq_sq (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (poleRankOneMat L mode *ᵥ ξ)
      = (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (poleVec L mode ⬝ᵥ ξ) ^ 2 := by
  have h1 : ξ ⬝ᵥ (poleRankOneMat L mode *ᵥ ξ)
      = ∑ i, ξ i * ((2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * poleVec L mode i * (poleVec L mode ⬝ᵥ ξ)) :=
    Finset.sum_congr rfl fun i _ => by rw [poleRankOneMat_mulVec]
  have h2 : (∑ i, ξ i * ((2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * poleVec L mode i * (poleVec L mode ⬝ᵥ ξ)))
      = (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (∑ i, poleVec L mode i * ξ i) * (poleVec L mode ⬝ᵥ ξ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  change (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (poleVec L mode ⬝ᵥ ξ) * (poleVec L mode ⬝ᵥ ξ)
    = (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * (poleVec L mode ⬝ᵥ ξ) ^ 2
  ring

/-! ### The zero mode index `zeroIdx` and high-mode lower bounds outside `modeCutoffSet` -/

/-- **The zero-mode index** `none : Cvs.Finite.SymmetricModeSet.Idx N`. -/
def zeroIdx (N : ℕ) : Cvs.Finite.SymmetricModeSet.Idx N := none

/-- `Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N) = 0`. -/
theorem mode_zeroIdx (N : ℕ) : Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N) = 0 := rfl

/-- `zeroIdx N` belongs to `modeCutoffSet N M₀` for every `N M₀ : ℕ`. -/
theorem zeroIdx_mem_modeCutoffSet (N M₀ : ℕ) :
    zeroIdx N ∈ modeCutoffSet N M₀ := by
  change (Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N)).natAbs ≤ M₀
  simp [mode_zeroIdx]

/-- For any integer `z : ℤ`, `|(z : ℝ)| = (z.natAbs : ℝ)`. -/
theorem abs_int_cast_eq_natAbs (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
  have h : (z.natAbs : ℤ) = z ∨ (z.natAbs : ℤ) = -z := by omega
  rcases h with h | h
  · have h' : ((z.natAbs : ℤ) : ℝ) = (z : ℝ) := by exact_mod_cast h
    simp only [Int.cast_natCast] at h'
    rw [← h', abs_of_nonneg (Nat.cast_nonneg _)]
  · have h' : ((z.natAbs : ℤ) : ℝ) = -(z : ℝ) := by exact_mod_cast h
    simp only [Int.cast_natCast] at h'
    have h'' : (z : ℝ) = -(z.natAbs : ℝ) := by linarith
    rw [h'', abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

/-- For `i ∉ modeCutoffSet N M₀`, `M₀ + 1 ≤ (mode N i).natAbs`. -/
theorem succ_le_natAbs_mode_of_not_mem_modeCutoffSet {N M₀ : ℕ} {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : i ∉ modeCutoffSet N M₀) :
    M₀ + 1 ≤ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs := by
  change ¬ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀ at hi
  omega

/-- For `i ∉ modeCutoffSet N M₀`, `(M₀ : ℝ) + 1 ≤ |(mode N i : ℝ)|`. -/
theorem one_add_le_abs_mode_of_not_mem_modeCutoffSet {N M₀ : ℕ} {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : i ∉ modeCutoffSet N M₀) :
    (M₀ : ℝ) + 1 ≤ |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| := by
  rw [abs_int_cast_eq_natAbs]
  exact_mod_cast succ_le_natAbs_mode_of_not_mem_modeCutoffSet hi

/-- For `i ∉ modeCutoffSet N M₀`, `0 < |(mode N i : ℝ)|`. -/
theorem abs_mode_pos_of_not_mem_modeCutoffSet {N M₀ : ℕ} {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : i ∉ modeCutoffSet N M₀) :
    0 < |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| := by
  have h1 := one_add_le_abs_mode_of_not_mem_modeCutoffSet hi
  have h0 : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  linarith

/-! ### High-mode pointwise and `ℓ²` tail bounds for `poleVec` outside `modeCutoffSet` -/

/-- Sharp high-mode pointwise bound on `poleVec` outside `modeCutoffSet N M₀` (with denominator `8π²`). -/
theorem poleVec_le_of_not_mem_modeCutoffSet_eight {L : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ modeCutoffSet N M₀) :
    poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i
      ≤ L ^ 2 / (8 * π ^ 2 * ((M₀ : ℝ) + 1)) * (1 / |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)|) := by
  set m : ℝ := (Cvs.Finite.SymmetricModeSet.mode N i : ℝ)
  have hm_ge : (M₀ : ℝ) + 1 ≤ |m| := one_add_le_abs_mode_of_not_mem_modeCutoffSet hi
  have hm_pos : 0 < |m| := abs_mode_pos_of_not_mem_modeCutoffSet hi
  have hm_ne : m ≠ 0 := abs_pos.1 hm_pos
  have hpi : 0 < π := Real.pi_pos
  have hω : 2 * π * m / L ≠ 0 := div_ne_zero (mul_ne_zero (by positivity) hm_ne) hL.ne'
  have huu := Cvs.Finite.OffDiagonalKernelDecay.uu_half_le_inv_two_sq hω
  have hrew : 1 / (2 * (2 * π * m / L) ^ 2) = L ^ 2 / (8 * π ^ 2) * (1 / |m| ^ 2) := by
    rw [sq_abs]
    field_simp [hL.ne', hpi.ne', hm_ne]
    ring
  have hMpos : 0 < (M₀ : ℝ) + 1 := by positivity
  have hmul : ((M₀ : ℝ) + 1) * |m| ≤ |m| ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hm_ge hm_pos.le
  have hinv : 1 / |m| ^ 2 ≤ 1 / (((M₀ : ℝ) + 1) * |m|) :=
    div_le_div_of_nonneg_left zero_le_one (mul_pos hMpos hm_pos) hmul
  have hstep : L ^ 2 / (8 * π ^ 2) * (1 / |m| ^ 2)
      ≤ L ^ 2 / (8 * π ^ 2) * (1 / (((M₀ : ℝ) + 1) * |m|)) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hrhs : L ^ 2 / (8 * π ^ 2) * (1 / (((M₀ : ℝ) + 1) * |m|))
      = L ^ 2 / (8 * π ^ 2 * ((M₀ : ℝ) + 1)) * (1 / |m|) := by
    field_simp [hpi.ne', hMpos.ne', hm_pos.ne']
  unfold poleVec
  linarith

/-- Sharp squared high-mode bound on `poleVec` outside `modeCutoffSet N M₀` (with denominator `8π⁴`). -/
theorem poleVec_sq_le_of_not_mem_modeCutoffSet_eight {L : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ modeCutoffSet N M₀) :
    (poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i) ^ 2
      ≤ L ^ 4 / (8 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2)
        * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N) : ℝ)) ^ 2) := by
  have h0 : 0 ≤ poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i := poleVec_nonneg L (Cvs.Finite.SymmetricModeSet.mode N) i
  have hle := poleVec_le_of_not_mem_modeCutoffSet_eight hL hi
  have hsq : (poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i) ^ 2
      ≤ (L ^ 2 / (8 * π ^ 2 * ((M₀ : ℝ) + 1)) * (1 / |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)|)) ^ 2 := by
    nlinarith
  have hpi0 : 0 < π := Real.pi_pos
  have hMpos : 0 < (M₀ : ℝ) + 1 := by positivity
  have hm_ne : (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ≠ 0 := abs_pos.1 (abs_mode_pos_of_not_mem_modeCutoffSet hi)
  have hrhs : (L ^ 2 / (8 * π ^ 2 * ((M₀ : ℝ) + 1)) * (1 / |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)|)) ^ 2
      = L ^ 4 / (64 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2)
        * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N) : ℝ)) ^ 2) := by
    rw [mode_zeroIdx, Int.cast_zero, sub_zero, mul_pow, one_div_pow, sq_abs]
    field_simp [hpi0.ne', hMpos.ne', hm_ne]
    ring
  rw [hrhs] at hsq
  have hpi : 0 < π ^ 4 * ((M₀ : ℝ) + 1) ^ 2 := by positivity
  have h64 : L ^ 4 / (64 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2)
      ≤ L ^ 4 / (8 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    linarith
  exact hsq.trans (mul_le_mul_of_nonneg_right h64 (by positivity))

/-- Sharp `N`-independent high-mode `ℓ²` tail bound for `poleVec` outside `modeCutoffSet N M₀`
(with factor `L⁴ / (2π⁴ (M₀ + 1)²)`). -/
theorem sum_not_mem_modeCutoffSet_poleVec_sq_le_half {L : ℝ} (hL : 0 < L) (N M₀ : ℕ) :
    (∑ i ∈ Finset.univ.filter (· ∉ modeCutoffSet N M₀), (poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i) ^ 2)
      ≤ L ^ 4 / (2 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) := by
  have hle1 : (∑ i ∈ Finset.univ.filter (· ∉ modeCutoffSet N M₀), (poleVec L (Cvs.Finite.SymmetricModeSet.mode N) i) ^ 2)
      ≤ ∑ i ∈ Finset.univ.filter (· ∉ modeCutoffSet N M₀),
          L ^ 4 / (8 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2)
            * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N (zeroIdx N) : ℝ)) ^ 2) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact poleVec_sq_le_of_not_mem_modeCutoffSet_eight hL (Finset.mem_filter.1 hi).2
  rw [← Finset.mul_sum] at hle1
  have h4 := Cvs.Route.ModeSepSumUniformBound.sum_not_mem_inv_sq_le_four N (modeCutoffSet N M₀) (zeroIdx_mem_modeCutoffSet N M₀)
  rw [← Finset.sum_filter] at h4
  have hle2 := mul_le_mul_of_nonneg_left h4
    (show 0 ≤ L ^ 4 / (8 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) by positivity)
  have hpi : π ^ 4 * ((M₀ : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have hrhs : L ^ 4 / (8 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) * 4
      = L ^ 4 / (2 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) := by
    field_simp [hpi]
    ring
  linarith

/-! ### Bulk support and `poleRankOneMat` quadratic form bound on `modeCutoffRung` -/

/-- **Every bulk vector `w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)` vanishes on
`modeCutoffSet N M₀`.** -/
theorem apply_eq_zero_of_mem_modeCutoffSet {N M₀ : ℕ} {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w)
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∈ modeCutoffSet N M₀) :
    w i = 0 :=
  apply_eq_zero_of_evenBasisVec_mem_rung (Cvs.Finite.SymmetricModeSet.negI_involutive N) hw
    (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- For `w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`, the dot product `u ⬝ᵥ w` equals
`complVec (modeCutoffSet N M₀) u ⬝ᵥ w`. -/
theorem dotProduct_eq_complVec_dotProduct_of_bulk_modeCutoffRung {N M₀ : ℕ}
    (u : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    u ⬝ᵥ w = complVec (modeCutoffSet N M₀) u ⬝ᵥ w := by
  simp only [dotProduct, complVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ modeCutoffSet N M₀
  · simp [hi, apply_eq_zero_of_mem_modeCutoffSet hw hi]
  · simp [hi]

/-- Sharp bound on `(poleVec L (mode N) ⬝ᵥ w)²` for `w ∈ Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`
(with factor `L⁴ / (2π⁴ (M₀ + 1)²)`). -/
theorem dotProduct_poleVec_sq_le_half_of_bulk_modeCutoffRung {L : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (poleVec L (Cvs.Finite.SymmetricModeSet.mode N) ⬝ᵥ w) ^ 2
      ≤ L ^ 4 / (2 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) * (w ⬝ᵥ w) := by
  rw [dotProduct_eq_complVec_dotProduct_of_bulk_modeCutoffRung (poleVec L (Cvs.Finite.SymmetricModeSet.mode N)) hw]
  have hcs := dotProduct_sq_le_mul (complVec (modeCutoffSet N M₀) (poleVec L (Cvs.Finite.SymmetricModeSet.mode N))) w
  rw [complVec_dotProduct_self, ← Finset.sum_filter] at hcs
  have hsum := mul_le_mul_of_nonneg_right
    (sum_not_mem_modeCutoffSet_poleVec_sq_le_half hL N M₀) (dotProduct_self_nonneg w)
  exact hcs.trans hsum

/-- **`N`-independent `(M₀ + 1)⁻²` decay of the rank-one pole quadratic form on the bulk of `modeCutoffRung N M₀`**:
`w ⬝ᵥ (poleRankOneMat L (mode N) *ᵥ w) ≤ L³ * poleFactor L / (π⁴ (M₀ + 1)²) * (w ⬝ᵥ w)`. -/
theorem poleRankOneMat_bulk_modeCutoffRung_le {L : ℝ} (hL : 0 < L) {N M₀ : ℕ}
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    w ⬝ᵥ (poleRankOneMat L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)
      ≤ L ^ 3 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / (π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) * (w ⬝ᵥ w) := by
  rw [poleRankOneMat_quad_eq_sq]
  have hp : 0 ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L :=
    div_nonneg (mul_nonneg zero_le_two (Cvs.Route.PosChannelFloorCoercivity.poleFactor_nonneg L)) hL.le
  have h1 := mul_le_mul_of_nonneg_left
    (dotProduct_poleVec_sq_le_half_of_bulk_modeCutoffRung hL hw) hp
  have hrhs : (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
      * (L ^ 4 / (2 * π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) * (w ⬝ᵥ w))
      = L ^ 3 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / (π ^ 4 * ((M₀ : ℝ) + 1) ^ 2) * (w ⬝ᵥ w) := by
    have hpi : π ^ 4 * ((M₀ : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    field_simp [hL.ne', hpi]
  linarith

/-! ### `A1Mat` bulk floor and `A1Mat` cross-term bound on `modeCutoffRung N M₀` -/

/-- Whenever `L * exp(|C| + 30) ≤ M₀` and `i ∉ modeCutoffSet N M₀`, `C ≤ archSymbol(2π mode_N(i) / L)`. -/
theorem archSymbol_ge_of_not_mem_modeCutoffSet {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ modeCutoffSet N M₀) :
    C ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L) :=
  not_lt.1 (mt (fun h => lowModeSet_subset_modeCutoffSet hL N C hM₀ h) hi)

end Cvs.Route.HighModePoleTailDecay
