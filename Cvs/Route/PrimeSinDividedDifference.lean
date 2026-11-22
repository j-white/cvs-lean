import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HalfPoleMatrixModeBox
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.HighModeStripExcessFloor
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeSepSumUniformBound
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.Route.PrimeMatHilbertSchmidtTail
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# Divided-Difference `primeSin` Formula for `kPrime` and Oscillatory Cross-Term Bound

Expresses `kPrime` as the divided difference of `primeSin P R L ω := primeSum P R (sinCut L ω)` and
replaces `2 * primeWindowMass` by `B_sin` in the `modeCutoffRung` cross-term bound.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PrimeSinDividedDifference
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.DiagonalCutSymbol
open Cvs.Finite.OneModeEntries
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Finite.OffDiagonalKernelDecay
open Cvs.Route.PrimeMatHilbertSchmidtTail
open Cvs.Route.ModeSepSumUniformBound
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxGershgorinCriteria
open Cvs.Route.HighModePoleTailDecay
open Cvs.Route.HalfPoleMatrixModeBox
open Cvs.Route.HighModeStripExcessFloor

/-! ### The oscillatory prime sine sum `primeSin` and its divided-difference identity -/

/-- **The oscillatory prime sine polynomial** `primeSin P R L ω = primeSum P R (sinCut L ω)`. -/
def primeSin (P R : ℕ) (L ω : ℝ) : ℝ :=
  Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L ω)

/-- **Exact divided-difference formula for `Cvs.Finite.WindowMatrixSymbolKernel.kPrime`**: for `ω ≠ ω'`,
`kPrime P R L ω ω' = (primeSin P R L ω − primeSin P R L ω') / (ω − ω')`. -/
theorem kPrime_eq_sub_primeSin_div (P R : ℕ) (L : ℝ) {ω ω' : ℝ} (hne : ω ≠ ω') :
    Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L ω ω' = (primeSin P R L ω - primeSin P R L ω') / (ω - ω') := by
  symm
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kPrime primeSin Cvs.Finite.OneModeEntries.primeSum
  have h3 : ω - ω' ≠ 0 := sub_ne_zero.mpr hne
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hp' : p.Prime := (Finset.mem_filter.mp hp).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have ht : 0 < (r : ℝ) * Real.log p := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp'.one_lt)
    positivity
  rw [← Cvs.Finite.WindowMatrixSymbolKernel.dd_sinCut ht hne]
  field_simp

/-- **Exact mode divided-difference formula for `(1 / L) * kPrime`**: for `0 < L` and `m₁ ≠ m₂`,
`(1 / L) * kPrime P R L ω₁ ω₂ = (primeSin P R L ω₁ − primeSin P R L ω₂) / (2π (m₁ − m₂))`. -/
theorem one_div_L_mul_kPrime_mode_eq_sub_primeSin (P R : ℕ) {L : ℝ} (hL : 0 < L)
    {m₁ m₂ : ℤ} (hm : m₁ ≠ m₂) :
    1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * m₁ / L) (2 * π * m₂ / L)
      = (primeSin P R L (2 * π * m₁ / L) - primeSin P R L (2 * π * m₂ / L))
        / (2 * π * ((m₁ : ℝ) - m₂)) := by
  have hm_ne : (m₁ : ℝ) ≠ m₂ := by exact_mod_cast hm
  have hsub : (m₁ : ℝ) - m₂ ≠ 0 := sub_ne_zero.mpr hm_ne
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hω_sub : 2 * π * (m₁ : ℝ) / L - 2 * π * (m₂ : ℝ) / L
      = 2 * π * ((m₁ : ℝ) - m₂) / L := by ring
  have hne : 2 * π * (m₁ : ℝ) / L ≠ 2 * π * (m₂ : ℝ) / L := by
    intro h
    have h0 : 2 * π * ((m₁ : ℝ) - m₂) / L = 0 := by linarith
    have : 2 * π * ((m₁ : ℝ) - m₂) / L ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hsub) hL.ne'
    exact this h0
  rw [kPrime_eq_sub_primeSin_div P R L hne, hω_sub]
  field_simp [hL.ne', hpi, hsub]

/-- **Off-diagonal bound on `(1 / L) * kPrime` from a pointwise bound `B_sin` on `|primeSin|`.** -/
theorem abs_one_div_L_mul_kPrime_mode_le_of_primeSin_le (P R : ℕ) {L B_sin : ℝ} (hL : 0 < L)
    {m₁ m₂ : ℤ} (hm : m₁ ≠ m₂)
    (h1 : |primeSin P R L (2 * π * m₁ / L)| ≤ B_sin)
    (h2 : |primeSin P R L (2 * π * m₂ / L)| ≤ B_sin) :
    |1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * m₁ / L) (2 * π * m₂ / L)|
      ≤ B_sin / (π * |(m₁ : ℝ) - m₂|) := by
  have hm_ne : (m₁ : ℝ) ≠ m₂ := by exact_mod_cast hm
  have hm_pos : 0 < |(m₁ : ℝ) - m₂| := abs_pos.mpr (sub_ne_zero.mpr hm_ne)
  have hpi : 0 < π := Real.pi_pos
  have h2pi : 0 < 2 * π := by positivity
  rw [one_div_L_mul_kPrime_mode_eq_sub_primeSin P R hL hm, abs_div, abs_mul, abs_of_pos h2pi]
  have hnum : |primeSin P R L (2 * π * m₁ / L) - primeSin P R L (2 * π * m₂ / L)|
      ≤ 2 * B_sin := by
    have htri := abs_sub (primeSin P R L (2 * π * m₁ / L)) (primeSin P R L (2 * π * m₂ / L))
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (mul_pos h2pi hm_pos).le
  have hrhs : 2 * B_sin / (2 * π * |(m₁ : ℝ) - m₂|) = B_sin / (π * |(m₁ : ℝ) - m₂|) := by
    field_simp [hpi.ne', hm_pos.ne']
  linarith

/-! ### `ModePrimeSinBound` and oscillatory Hilbert–Schmidt `kPrimeMat` tail bounds -/

/-- **Pointwise bound `B_sin` on `|primeSin|` across the discrete modes `Cvs.Finite.SymmetricModeSet.Idx N`.** -/
def ModePrimeSinBound (P R : ℕ) (L : ℝ) (N : ℕ) (B_sin : ℝ) : Prop :=
  ∀ i : Cvs.Finite.SymmetricModeSet.Idx N, |primeSin P R L (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L)| ≤ B_sin

/-- Pointwise squared off-diagonal decay of `kPrimeMat` under `ModePrimeSinBound`:
`(kPrimeMat P R L (mode N) i j)² ≤ (B_sin / π)² * (1 / (mode_N(i) − mode_N(j))²)`. -/
theorem kPrimeMat_apply_sq_le_of_modePrimeSinBound {P R : ℕ} {L B_sin : ℝ} (hL : 0 < L)
    {N : ℕ} (hsin : ModePrimeSinBound P R L N B_sin)
    {S : Set (Cvs.Finite.SymmetricModeSet.Idx N)} {i j : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ S) (hj : j ∈ S) :
    (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) i j) ^ 2
      ≤ (B_sin / π) ^ 2 * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2) := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hmode : Cvs.Finite.SymmetricModeSet.mode N i ≠ Cvs.Finite.SymmetricModeSet.mode N j := fun h => hij (Cvs.Finite.SymmetricModeSet.mode_injective N h)
  have habs := abs_one_div_L_mul_kPrime_mode_le_of_primeSin_le P R hL hmode (hsin i) (hsin j)
  change |kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) i j|
    ≤ B_sin / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|) at habs
  have hsq : |kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) i j| ^ 2
      ≤ (B_sin / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)) ^ 2 := by
    nlinarith [abs_nonneg (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) i j)]
  rw [sq_abs] at hsq
  have hrhs : (B_sin / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)) ^ 2
      = (B_sin / π) ^ 2 * (1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2) := by
    have hdiv : B_sin / (π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|)
        = (B_sin / π) * (1 / |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j|) := by ring
    rw [hdiv, mul_pow, one_div_pow, sq_abs]
  linarith

/-- Under `ModePrimeSinBound`, the off-diagonal Hilbert–Schmidt sum of `kPrimeMat` is bounded by
`(B_sin / π)² * modeSepSum N S`. -/
theorem sum_not_mem_kPrimeMat_sq_le_modeSepSum_of_modePrimeSinBound
    {P R : ℕ} {L B_sin : ℝ} (hL : 0 < L) {N : ℕ}
    (hsin : ModePrimeSinBound P R L N B_sin)
    (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)] :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
      if i ∉ S then
        (∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if j ∈ S then (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) i j) ^ 2 else 0)
      else 0)
      ≤ (B_sin / π) ^ 2 * modeSepSum N S := by
  unfold modeSepSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, not_false_eq_true, ↓reduceIte, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceIte]
      exact kPrimeMat_apply_sq_le_of_modePrimeSinBound hL hsin hi hj
    · simp [hj]

/-- **Oscillatory Hilbert–Schmidt `kPrimeMat` tail bound on `modeCutoffRung N M₀`** (unfiltered sum form). -/
theorem kPrimeMat_tail_ite_modeCutoffRung_le_of_modePrimeSinBound
    {P R : ℕ} {L B_sin : ℝ} (hL : 0 < L) (_hB : 0 ≤ B_sin) {N M₀ : ℕ}
    (hsin : ModePrimeSinBound P R L N B_sin)
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
      if i ∉ modeCutoffSet N M₀ then
        (evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) i) ^ 2
      else 0)
      ≤ (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) := by
  have h1 := Cvs.Route.PrimeMatHilbertSchmidtTail.sum_not_mem_evenProjVec_sq_le (modeCutoffSet N M₀)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Route.ModeBoxIsometricTransfer.negI_mem_modeCutoffSet_iff N M₀)
    (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
  have hsupp : ∀ j, j ∉ modeCutoffSet N M₀ → r j = 0 :=
    fun _ hj => Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hj
  have h2 := Cvs.Route.PrimeMatHilbertSchmidtTail.sum_not_mem_mulVec_sq_le (modeCutoffSet N M₀)
    (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N)) hsupp
  have h3 := mul_le_mul_of_nonneg_right
    (sum_not_mem_kPrimeMat_sq_le_modeSepSum_of_modePrimeSinBound hL hsin (modeCutoffSet N M₀))
    (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r)
  have h4 := Cvs.Route.ModeSepSumUniformBound.modeSepSum_modeCutoffSet_le N M₀
  have hnonneg : 0 ≤ (B_sin / π) ^ 2 * (r ⬝ᵥ r) :=
    mul_nonneg (sq_nonneg _) (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r)
  have h5 := mul_le_mul_of_nonneg_left h4 hnonneg
  linarith

/-- **Oscillatory cross-term bound for `A1Mat` between `modeCutoffRung N M₀` and its bulk** under
`ModePrimeSinBound P R L N B_sin`. -/
theorem A1Mat_cross_sq_modeCutoffRung_le_of_modePrimeSinBound
    {P R : ℕ} {L B_sin : ℝ} (hL : 0 < L) (hB : 0 ≤ B_sin) {N M₀ : ℕ}
    (hsin : ModePrimeSinBound P R L N B_sin)
    {r w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀)
    (hw : Bulk (evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) (modeCutoffRung N M₀) w) :
    (r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) ^ 2
      ≤ (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) := by
  obtain ⟨z, hz, heq⟩ := Cvs.Route.LadderFreePrimeTailCoupling.exists_A1Mat_residual_eq_kPrime_tail hL P R N
    (modeCutoffSet N M₀) (Cvs.Route.ModeBoxIsometricTransfer.negI_mem_modeCutoffSet_iff N M₀) hr
  have hcs := Cvs.Route.PoleSlotRungResidual.dotProduct_symm_mulVec_sq_le_evenProjVec_sub_of_bulk
    (Cvs.Route.LadderFreePrimeTailCoupling.A1Mat_isSymm hL P R N) (Cvs.Finite.SymmetricModeSet.negI_involutive N) r hz hw
  rw [heq] at hcs
  have htail := mul_le_mul_of_nonneg_right
    (kPrimeMat_tail_ite_modeCutoffRung_le_of_modePrimeSinBound hL hB hsin hr)
    (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg w)
  exact hcs.trans htail

/-! ### Master discrete reductions with `ModePrimeSinBound` and `BulkStripExcess` -/

/-- **Even-sector positivity of `ApoleMat` from a `modeCutoffRung N M₀` floor of `ApoleHalfMat`,
`BulkStripExcess`, and `ModePrimeSinBound`.** -/
theorem ApoleMat_even_nonneg_of_modeCutoffRung_ApoleHalfMat_bulkStripExcess_primeSin
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {N M₀ : ℕ} {C B_strip B_sin cR : ℝ}
    (hb : 0 ≤ apoleBulkConstGen L C B_strip M₀) (hBsin : 0 ≤ B_sin) (hcR : 0 ≤ cR)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : BulkStripExcess P R L N M₀ B_strip)
    (hsin : ModePrimeSinBound P R L N B_sin)
    (hrung : ∀ r ∈ modeCutoffRung N M₀,
      cR * (r ⬝ᵥ r) ≤ r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r))
    (hsep : (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cR * apoleBulkConstGen L C B_strip M₀) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.ApoleMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  intro ξ hξ
  obtain ⟨r, hr, w, hw, rfl⟩ :=
    Cvs.Route.EvenMatrixSlotPoleRestored.exists_dec (modeCutoffRung_le_evenModeSub N M₀) ξ hξ
  have hsplit := ApoleMat_add_quad_ge_ApoleHalfMat hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) r w
  have hr_floor : cR * (r ⬝ᵥ r) ≤ r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := hrung r hr
  have hw_floor := A1Mat_sub_poleRankOneMat_bulk_ge_of_bulkStripExcess hL hM₀ hstrip hw
  have hrr : 0 ≤ r ⬝ᵥ r := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg r
  have hww : 0 ≤ w ⬝ᵥ w := Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg w
  have hA : 0 ≤ r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) :=
    le_trans (mul_nonneg hcR hrr) hr_floor
  have hW : 0 ≤ w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) -
      w ⬝ᵥ (poleRankOneMat L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
    le_trans (mul_nonneg hb hww) hw_floor
  have hcross := A1Mat_cross_sq_modeCutoffRung_le_of_modePrimeSinBound hL hBsin hsin hr hw
  have hprod1 :
      (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1)) * (r ⬝ᵥ r) * (w ⬝ᵥ w) ≤
        (cR * (r ⬝ᵥ r)) * (apoleBulkConstGen L C B_strip M₀ * (w ⬝ᵥ w)) := by
    have hmul := mul_le_mul_of_nonneg_right hsep (mul_nonneg hrr hww)
    linarith
  have hprod2 :
      (cR * (r ⬝ᵥ r)) * (apoleBulkConstGen L C B_strip M₀ * (w ⬝ᵥ w)) ≤
        (r ⬝ᵥ (ApoleHalfMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)) *
          (w ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) -
            w ⬝ᵥ (poleRankOneMat L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w)) :=
    mul_le_mul hr_floor hw_floor (mul_nonneg hb hww) hA
  have hquad := Cvs.Route.PoleSlotRungResidual.quad_nonneg_of_sq_le hA hW (le_trans hcross (le_trans hprod1 hprod2))
  linarith

end Cvs.Route.PrimeSinDividedDifference
