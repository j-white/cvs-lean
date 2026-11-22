import Mathlib
import Cvs.Finite.EvenGramSymmetryBridges
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenGramRungFloors
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.HighModeStripExcessFloor
import Cvs.Route.HighModeTailArchFree
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeSepSumUniformBound
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.Route.PrimeMatHilbertSchmidtTail
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.InsideFunctionTame
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# Full-`M` `ModeBox M₀` Reduction with `Fgen` Divided-Difference Coupling

Combines isometric `ModeBox M₀` transfer of `Cvs.Finite.TruncationQuadraticForm.M` with the pole-free `A1Mat ≤ M` bulk floor and
the `Cvs.Finite.WindowMatrixSymbolKernel.Fgen` divided-difference bound on off-diagonal entries of `Cvs.Finite.TruncationQuadraticForm.M`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxFgenCoupling
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Off-diagonal divided-difference identity for `Cvs.Finite.TruncationQuadraticForm.M` via `Cvs.Finite.WindowMatrixSymbolKernel.Fgen` -/

/-- **Off-diagonal divided-difference formula for `Cvs.Finite.TruncationQuadraticForm.M`**: for `0 < L`, injective `mode`, and `i ≠ j`,
`Cvs.Finite.TruncationQuadraticForm.M P R L mode i j = (Fgen P R L ω_i - Fgen P R L ω_j) / (2π (mode j - mode i))`. -/
theorem M_apply_of_ne_eq_sub_Fgen {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) {i j : ι} (hij : i ≠ j) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i j =
      (Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode i / L) - Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode j / L)) /
        (2 * π * ((mode j : ℝ) - mode i)) := by
  rw [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R hinj i j, if_neg hij, zero_add]
  have hmn : mode i ≠ mode j := fun h => hij (hinj h)
  have hm_ne : (mode i : ℝ) ≠ mode j := by exact_mod_cast hmn
  have hsub : (mode j : ℝ) - mode i ≠ 0 := sub_ne_zero.mpr hm_ne.symm
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hω_sub : 2 * π * (mode j : ℝ) / L - 2 * π * (mode i : ℝ) / L =
      2 * π * ((mode j : ℝ) - mode i) / L := by ring
  have hne : 2 * π * (mode i : ℝ) / L ≠ 2 * π * (mode j : ℝ) / L := by
    intro h
    have h0 : 2 * π * ((mode j : ℝ) - mode i) / L = 0 := by linarith
    have : 2 * π * ((mode j : ℝ) - mode i) / L ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hsub) hL.ne'
    exact this h0
  rw [← Cvs.Finite.WindowMatrixSymbolKernel.dd_Fgen P R hL hne, hω_sub]
  field_simp [hL.ne', hpi, hsub]

/-- **Off-diagonal bound on `Cvs.Finite.TruncationQuadraticForm.M` from a pointwise bound `B_fgen` on `|Cvs.Finite.WindowMatrixSymbolKernel.Fgen|`.** -/
theorem abs_M_apply_of_ne_le_of_Fgen_le {L B_fgen : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) {i j : ι} (hij : i ≠ j)
    (h1 : |Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode i / L)| ≤ B_fgen)
    (h2 : |Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode j / L)| ≤ B_fgen) :
    |Cvs.Finite.TruncationQuadraticForm.M P R L mode i j| ≤ B_fgen / (π * |(mode i : ℝ) - mode j|) := by
  have hmn : mode i ≠ mode j := fun h => hij (hinj h)
  have hm_ne : (mode i : ℝ) ≠ mode j := by exact_mod_cast hmn
  have hm_pos : 0 < |(mode i : ℝ) - mode j| := abs_pos.mpr (sub_ne_zero.mpr hm_ne)
  have hpi : 0 < π := Real.pi_pos
  have h2pi : 0 < 2 * π := by positivity
  rw [M_apply_of_ne_eq_sub_Fgen hL P R hinj hij, abs_div, abs_mul, abs_of_pos h2pi,
    abs_sub_comm (mode j : ℝ) (mode i : ℝ)]
  have hnum : |Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode i / L) - Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode j / L)|
      ≤ 2 * B_fgen := by
    have htri := abs_sub (Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode i / L))
      (Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * mode j / L))
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (mul_pos h2pi hm_pos).le
  have hrhs : 2 * B_fgen / (2 * π * |(mode i : ℝ) - mode j|) =
      B_fgen / (π * |(mode i : ℝ) - mode j|) := by
    field_simp [hpi.ne', hm_pos.ne']
  linarith

/-! ### `N`-independent integer-mode bound `IntModeFgenBound` and full-`M` cross-term bound -/

/-- **`N`-independent integer-mode bound on `|Cvs.Finite.WindowMatrixSymbolKernel.Fgen|` across all `m : ℤ`.** -/
def IntModeFgenBound (P R : ℕ) (L B_fgen : ℝ) : Prop :=
  ∀ m : ℤ, |Cvs.Finite.WindowMatrixSymbolKernel.Fgen P R L (2 * π * (m : ℝ) / L)| ≤ B_fgen

/-- Any `B_fgen` satisfying `IntModeFgenBound P R L B_fgen` is nonnegative. -/
theorem intModeFgenBound_nonneg {P R : ℕ} {L B_fgen : ℝ}
    (h : IntModeFgenBound P R L B_fgen) : 0 ≤ B_fgen :=
  (abs_nonneg _).trans (h 0)

/-- Pointwise squared off-diagonal decay of `Cvs.Finite.TruncationQuadraticForm.M` under `IntModeFgenBound`:
`(Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i j)² ≤ (B_fgen / π)² * (1 / (mode_N(i) − mode_N(j))²)`. -/
theorem M_apply_sq_le_of_intModeFgenBound {P R : ℕ} {L B_fgen : ℝ} (hL : 0 < L)
    (hF : IntModeFgenBound P R L B_fgen)
    {N : ℕ} {S : Set (Cvs.Finite.SymmetricModeSet.Idx N)} {i j : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ S) (hj : j ∈ S) :
    (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i j) ^ 2
      ≤ (B_fgen / π) ^ 2 * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2) := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have habs := abs_M_apply_of_ne_le_of_Fgen_le hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) hij
    (hF (Cvs.Finite.SymmetricModeSet.mode N i)) (hF (Cvs.Finite.SymmetricModeSet.mode N j))
  have hsq : |Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i j| ^ 2
      ≤ (B_fgen / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)) ^ 2 := by
    nlinarith [abs_nonneg (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i j)]
  rw [sq_abs] at hsq
  have hrhs : (B_fgen / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)) ^ 2
      = (B_fgen / π) ^ 2 * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2) := by
    have hdiv : B_fgen / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)
        = (B_fgen / π) * (1 / |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|) := by ring
    rw [hdiv, mul_pow, one_div_pow, sq_abs]
  linarith

/-- Under `IntModeFgenBound`, the off-diagonal Hilbert–Schmidt sum of `Cvs.Finite.TruncationQuadraticForm.M` is bounded by
`(B_fgen / π)² * modeSepSum N S`. -/
theorem sum_not_mem_M_sq_le_modeSepSum_of_intModeFgenBound
    {P R : ℕ} {L B_fgen : ℝ} (hL : 0 < L)
    (hF : IntModeFgenBound P R L B_fgen)
    (N : ℕ) (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)] :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
      if i ∉ S then
        (∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if j ∈ S then (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i j) ^ 2 else 0)
      else 0)
      ≤ (B_fgen / π) ^ 2 * modeSepSum N S := by
  unfold modeSepSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, not_false_eq_true, ↓reduceIte, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceIte]
      exact M_apply_sq_le_of_intModeFgenBound hL hF hi hj
    · simp [hj]

/-- Exact high-mode tail formula for the residual of any even mode vector `v` modulo a
`negI N`-invariant mode set `S`. -/
theorem exists_even_residual_eq_tail (N : ℕ)
    (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)]
    (hS : ∀ i, Cvs.Finite.SymmetricModeSet.negI N i ∈ S ↔ i ∈ S)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hv : v ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) :
    ∃ z ∈ Submodule.span ℝ (evenBasisVec (Cvs.Finite.SymmetricModeSet.negI N) '' S),
      ((v - z) ⬝ᵥ (v - z))
        = ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if i ∉ S then (v i) ^ 2 else 0 := by
  refine ⟨restrictVec S v,
    restrictVec_mem_span_evenBasisVec S (Cvs.Finite.SymmetricModeSet.negI_involutive N) hS hv, ?_⟩
  rw [← complVec_eq_sub_restrictVec S v, complVec_dotProduct_self S v]

/-- **Hilbert–Schmidt high-mode tail bound for `Cvs.Finite.TruncationQuadraticForm.M` on `modeCutoffRung N M₀`** under
`IntModeFgenBound`. -/
theorem M_tail_ite_modeCutoffRung_le_of_intModeFgenBound
    {P R : ℕ} {L B_fgen : ℝ} (hL : 0 < L)
    (hF : IntModeFgenBound P R L B_fgen) {N M₀ : ℕ}
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
      if i ∉ modeCutoffSet N M₀ then
        (evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) i) ^ 2
      else 0)
      ≤ (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) := by
  have h1 := Cvs.Route.PrimeMatHilbertSchmidtTail.sum_not_mem_evenProjVec_sq_le (modeCutoffSet N M₀)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Route.ModeBoxIsometricTransfer.negI_mem_modeCutoffSet_iff N M₀)
    (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
  have hsupp : ∀ j, j ∉ modeCutoffSet N M₀ → r j = 0 :=
    fun _ hj => Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hj
  have h2 := Cvs.Route.PrimeMatHilbertSchmidtTail.sum_not_mem_mulVec_sq_le (modeCutoffSet N M₀)
    (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)) hsupp
  have h3 := mul_le_mul_of_nonneg_right
    (sum_not_mem_M_sq_le_modeSepSum_of_intModeFgenBound hL hF N (modeCutoffSet N M₀))
    (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r)
  have h4 := Cvs.Route.ModeSepSumUniformBound.modeSepSum_modeCutoffSet_le N M₀
  have hnonneg : 0 ≤ (B_fgen / π) ^ 2 * (r ⬝ᵥ r) :=
    mul_nonneg (sq_nonneg _) (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r)
  have h5 := mul_le_mul_of_nonneg_left h4 hnonneg
  linarith

/-- **Cross-term bound for `Cvs.Finite.TruncationQuadraticForm.M` between `modeCutoffRung N M₀` and its bulk** under
`IntModeFgenBound P R L B_fgen`. -/
theorem M_cross_sq_modeCutoffRung_le_of_intModeFgenBound
    {P R : ℕ} {L B_fgen : ℝ} (hL : 0 < L)
    (hF : IntModeFgenBound P R L B_fgen) {N M₀ : ℕ}
    {r w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀)
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) ^ 2
      ≤ (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) := by
  have hv : evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) ∈
      evenModeSub (Cvs.Finite.SymmetricModeSet.negI N) :=
    evenProjVec_mem_evenModeSub (Cvs.Finite.SymmetricModeSet.negI_involutive N) _
  obtain ⟨z, hz, heq⟩ := exists_even_residual_eq_tail N
    (modeCutoffSet N M₀) (Cvs.Route.ModeBoxIsometricTransfer.negI_mem_modeCutoffSet_iff N M₀) hv
  have hcs := Cvs.Route.PoleSlotRungResidual.dotProduct_symm_mulVec_sq_le_evenProjVec_sub_of_bulk
    (Cvs.StepA.OddAboveDisplacement.M_isSymm hL P R N) (Cvs.Finite.SymmetricModeSet.negI_involutive N) r hz hw
  rw [heq] at hcs
  have htail := mul_le_mul_of_nonneg_right
    (M_tail_ite_modeCutoffRung_le_of_intModeFgenBound hL hF hr)
    (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg w)
  exact hcs.trans htail

/-! ### Pole-free bulk floor of `Cvs.Finite.TruncationQuadraticForm.M` and master full-`M` `ModeBox M₀` reductions -/

/-- Pole-free high-mode bulk floor constant `a1BulkConstGen C B_strip = C - B_strip`. -/
def a1BulkConstGen (C B_strip : ℝ) : ℝ :=
  C - B_strip

/-- On `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`, `w ⬝ᵥ (A1Mat *ᵥ w)` is bounded below by
`a1BulkConstGen C B_strip * (w ⬝ᵥ w)`. -/
theorem A1Mat_bulk_ge_of_bulkStripExcess
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    a1BulkConstGen C B_strip * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
  Cvs.Route.HighModeStripExcessFloor.A1Mat_bulkFloor_modeCutoffRung_of_bulkStripExcess hL hM₀ hstrip hw

/-- **On `Bulk (evenModeSub (negI N)) (modeCutoffRung N M₀)`, `w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M *ᵥ w)` is bounded below
by `a1BulkConstGen C B_strip * (w ⬝ᵥ w)` without any pole subtraction.** -/
theorem M_bulk_ge_of_bulkStripExcess
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip : ℝ}
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    a1BulkConstGen C B_strip * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
  (A1Mat_bulk_ge_of_bulkStripExcess hL hM₀ hstrip hw).trans
    (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat_le_M hL P R (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hw.1)

/-- **Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` from a `modeCutoffRung N M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`,
`BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem M_even_nonneg_of_modeCutoffRung_M_floor_fgen
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip B_fgen cM : ℝ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    (hF : IntModeFgenBound P R L B_fgen)
    (hrung : ∀ r ∈ modeCutoffRung N M₀,
      cM * (r ⬝ᵥ r) ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip) :
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
  have hw_floor := M_bulk_ge_of_bulkStripExcess hL hM₀ hstrip hw
  have hrr : 0 ≤ r ⬝ᵥ r := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r
  have hww : 0 ≤ w ⬝ᵥ w := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg w
  have hA : 0 ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) :=
    le_trans (mul_nonneg hcM hrr) hr_floor
  have hW : 0 ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
    le_trans (mul_nonneg hb hww) hw_floor
  have hcross := M_cross_sq_modeCutoffRung_le_of_intModeFgenBound hL hF hr hw
  have hprod1 :
      (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) ≤
        (cM * (r ⬝ᵥ r)) * (a1BulkConstGen C B_strip * (w ⬝ᵥ w)) := by
    have hmul := mul_le_mul_of_nonneg_right hsep (mul_nonneg hrr hww)
    linarith
  have hprod2 :
      (cM * (r ⬝ᵥ r)) * (a1BulkConstGen C B_strip * (w ⬝ᵥ w)) ≤
        (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)) *
          (w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) :=
    mul_le_mul hr_floor hw_floor (mul_nonneg hb hww) hA
  have hquad := Cvs.Route.PoleSlotRungResidual.quad_nonneg_of_sq_le hA hW (le_trans hcross (le_trans hprod1 hprod2))
  linarith

/-- **Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)` for all `N : ℕ` from a single `ModeBox M₀`
floor of `Cvs.Finite.TruncationQuadraticForm.M`, `BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem M_even_nonneg_of_modeBox_M_floor_fgen
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {M₀ : ℕ} {C B_strip B_fgen cM : ℝ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess P R L N M₀ B_strip)
    (hF : IntModeFgenBound P R L B_fgen)
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η) ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip)
    (N : ℕ) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) :=
  M_even_nonneg_of_modeCutoffRung_M_floor_fgen hL hb hcM hM₀ (hstrip N) hF
    (modeCutoffRung_M_floor_of_modeBox P R N M₀ L cM hrung) hsep

/-- **Continuous even form positivity on `evenSub hL.le` from a single `ModeBox M₀` floor of
`Cvs.Finite.TruncationQuadraticForm.M`, `BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem Q_evenSub_nonneg_of_modeBox_M_floor_fgen
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {M₀ : ℕ} {C B_strip B_fgen cM : ℝ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess P R L N M₀ B_strip)
    (hF : IntModeFgenBound P R L B_fgen)
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η) ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip) :
    ∀ φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le, 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ :=
  fun _ hφ => Cvs.Route.EvenMatrixSlotPoleRestored.Q_evenSub_nonneg_of_M_even_nonneg hL P R
    (M_even_nonneg_of_modeBox_M_floor_fgen hL hb hcM hM₀ hstrip hF hrung hsep) hφ

/-- **Continuous even window positivity `∀ v ∈ Ev x, 0 ≤ Qx x v` at `x ≥ 2` from a single
`ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`, `BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem Qx_Ev_nonneg_of_modeBox_M_floor_fgen {x : ℕ} (hx : 2 ≤ x)
    {C B_strip B_fgen cM : ℝ} {M₀ : ℕ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip)
    (hF : IntModeFgenBound x (Nat.clog 2 x) (Real.log x) B_fgen)
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η)
        ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  exact (Cvs.Route.EvenMatrixSlotPoleRestored.Qx_Ev_nonneg_iff_M_even_nonneg hx).2
    (M_even_nonneg_of_modeBox_M_floor_fgen hL hb hcM hM₀ hstrip hF hrung hsep)

/-- **`EvenGramNonneg x` at `x ≥ 2` from a single `ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`,
`BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem evenGramNonneg_of_modeBox_M_floor_fgen {x : ℕ} (hx : 2 ≤ x)
    {C B_strip B_fgen cM : ℝ} {M₀ : ℕ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip)
    (hF : IntModeFgenBound x (Nat.clog 2 x) (Real.log x) B_fgen)
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η)
        ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip) :
    EvenGramNonneg x :=
  evenGramNonneg_of_evenWindowPos
    (Qx_Ev_nonneg_of_modeBox_M_floor_fgen hx hb hcM hM₀ hstrip hF hrung hsep)

/-- **`ReflBound x 1 1` at `80 ≤ 2πx` from a single `ModeBox M₀` floor of `Cvs.Finite.TruncationQuadraticForm.M`,
`BulkStripExcess`, and `IntModeFgenBound`.** -/
theorem reflBound_one_of_modeBox_M_floor_fgen {x : ℕ} (hx : 80 ≤ 2 * π * x)
    {C B_strip B_fgen cM : ℝ} {M₀ : ℕ}
    (hb : 0 ≤ a1BulkConstGen C B_strip) (hcM : 0 ≤ cM)
    (hM₀ : Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip)
    (hF : IntModeFgenBound x (Nat.clog 2 x) (Real.log x) B_fgen)
    (hrung : ∀ η ∈ evenModeSub (negBox M₀),
      cM * (η ⬝ᵥ η)
        ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η))
    (hsep : (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cM * a1BulkConstGen C B_strip) :
    ReflBound x 1 1 :=
  (evenGramNonneg_iff_reflBound_one hx).1
    (evenGramNonneg_of_modeBox_M_floor_fgen
      (Cvs.WeilForm.InsideFunctionTame.two_le_of_scale hx) hb hcM hM₀ hstrip hF hrung hsep)

/-- **Master full-`M` `ModeBox M₀` reduction for `RiemannHypothesis`**:
uses the full CvS matrix `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀`, the pole-free bulk constant `a1BulkConstGen C B_strip`,
and the `Cvs.Finite.WindowMatrixSymbolKernel.Fgen` divided-difference bound `IntModeFgenBound`. -/
theorem riemannHypothesis_of_modeBox_M_floor_fgen
    (h : ∃ᶠ x : ℕ in atTop,
      ∃ (C B_strip B_fgen cM : ℝ) (M₀ : ℕ),
        0 ≤ a1BulkConstGen C B_strip ∧
        0 ≤ cM ∧
        Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ) ∧
        (∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip) ∧
        IntModeFgenBound x (Nat.clog 2 x) (Real.log x) B_fgen ∧
        (∀ η ∈ evenModeSub (negBox M₀),
          cM * (η ⬝ᵥ η)
            ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ η)) ∧
        (B_fgen / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
          ≤ cM * a1BulkConstGen C B_strip) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_)
  obtain ⟨C, B_strip, B_fgen, cM, M₀, hb, hcM, hM₀, hstrip, hF, hrung, hsep⟩ := hx
  exact Qx_Ev_nonneg_of_modeBox_M_floor_fgen hx2 hb hcM hM₀ hstrip hF hrung hsep

end Cvs.Route.ModeBoxFgenCoupling
