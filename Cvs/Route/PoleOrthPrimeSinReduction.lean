import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FejerPrimeCosineSymbol
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HalfPoleMatrixModeBox
import Cvs.Route.HighModeStripExcessFloor
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.PoleOrthogonalSubspace
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PrimeSinDividedDifference
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# Unified `A1Mat`-Only `poleOrthSub` Reduction with `IntModePrimeSinBound`

Unifies `Cvs.Route.PrimeSinDividedDifference` and `Cvs.Route.FejerPrimeCosineSymbol` to eliminate `ApoleHalfMat` from the `ModeBox M₀` hypotheses and
replaces `∀ N, ModePrimeSinBound` by the `N`-independent `IntModePrimeSinBound`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PoleOrthPrimeSinReduction
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.LadderFreePrimeTailCoupling
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxGershgorinCriteria
open Cvs.Route.HighModePoleTailDecay
open Cvs.Route.HalfPoleMatrixModeBox
open Cvs.Route.PoleOrthogonalSubspace
open Cvs.Route.HighModeStripExcessFloor
open Cvs.Route.PrimeSinDividedDifference
open Cvs.Route.FejerPrimeCosineSymbol

/-! ### `N`-independent integer-mode prime sine bound `IntModePrimeSinBound` -/

/-- **`N`-independent integer-mode bound on `|primeSin|` across all `m : ℤ`.** -/
def IntModePrimeSinBound (P R : ℕ) (L B_sin : ℝ) : Prop :=
  ∀ m : ℤ, |primeSin P R L (2 * π * (m : ℝ) / L)| ≤ B_sin

/-- Any `B_sin` satisfying `IntModePrimeSinBound P R L B_sin` is nonnegative. -/
theorem intModePrimeSinBound_nonneg {P R : ℕ} {L B_sin : ℝ}
    (h : IntModePrimeSinBound P R L B_sin) : 0 ≤ B_sin :=
  (abs_nonneg _).trans (h 0)

/-- `IntModePrimeSinBound P R L B_sin` implies `ModePrimeSinBound P R L N B_sin` for every `N : ℕ`. -/
theorem modePrimeSinBound_of_intModePrimeSinBound {P R : ℕ} {L B_sin : ℝ}
    (h : IntModePrimeSinBound P R L B_sin) (N : ℕ) :
    ModePrimeSinBound P R L N B_sin :=
  fun i => h (Cvs.Finite.SymmetricModeSet.mode N i)

/-! ### Elimination of `ApoleHalfMat` from the `ModeBox M₀` hypotheses via `Cvs.Route.FejerPrimeCosineSymbol` -/

/-- Lower bound on the pole slack `boxPoleVec ⬝ᵥ (ApoleHalfMat *ᵥ boxPoleVec) − cR * ‖boxPoleVec‖²`
purely in terms of the `A1Mat` Rayleigh quotient `cA` and `4 * poleFactor L / L`. -/
theorem boxPoleVec_ApoleHalfMat_sub_ge_of_A1Mat_ge {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    {cA cR : ℝ}
    (hcA : cA * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀)) :
    (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L - cR) * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀)
        - cR * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀) := by
  have h1 := Cvs.Route.FejerPrimeCosineSymbol.boxPoleVec_ApoleHalfMat_quad_ge_of_A1Mat_ge hL P R M₀ hcA
  linarith

/-- **Pure `A1Mat` reduction of the `ModeBox M₀` floor of `ApoleHalfMat`**:
completely eliminates `ApoleHalfMat` from the hypotheses on `poleOrthSub L M₀` and `boxPoleVec L M₀`. -/
theorem modeBox_ApoleHalfMat_floor_of_poleOrthSub_A1Mat_only
    {P R M₀ : ℕ} {L cA cR δ : ℝ} (hL : 0 < L) (hcR : 0 ≤ cR) (hδ : 0 ≤ δ)
    (hcR_le : cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
    (horth : ∀ ζ ∈ poleOrthSub L M₀,
      (cR + δ) * (ζ ⬝ᵥ ζ) ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))
    (hpole : cA * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀))
    (hcross : ∀ ζ ∈ poleOrthSub L M₀,
      (boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)) ^ 2
        ≤ (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L - cR)
          * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀) * (δ * (ζ ⬝ᵥ ζ)))
    (η : ModeBox M₀ → ℝ) (hη : η ∈ evenModeSub (negBox M₀)) :
    cR * (η ⬝ᵥ η) ≤ η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ η) := by
  refine modeBox_ApoleHalfMat_floor_of_poleOrthSub_A1Mat_floor hL hcR hδ horth
    (Cvs.Route.FejerPrimeCosineSymbol.boxPoleVec_ApoleHalfMat_floor_of_A1Mat_ge hL P R M₀ hpole hcR_le)
    (fun ζ hζ => (hcross ζ hζ).trans ?_) η hη
  exact mul_le_mul_of_nonneg_right
    (boxPoleVec_ApoleHalfMat_sub_ge_of_A1Mat_ge hL P R M₀ hpole)
    (mul_nonneg hδ (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg ζ))

/-! ### Master `A1Mat`-only reductions for `ApoleMat`, `Cvs.Finite.TruncationQuadraticForm.M`, `Qx`, and `RiemannHypothesis` -/

/-- **Even-sector positivity of `ApoleMat` for all `N : ℕ` from pure `A1Mat` bounds on `ModeBox M₀`,
`BulkStripExcess`, and `IntModePrimeSinBound`.** -/
theorem ApoleMat_even_nonneg_of_poleOrthSub_A1Mat_only
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {M₀ : ℕ} {C B_strip B_sin cA cR δ : ℝ}
    (hb : 0 ≤ apoleBulkConstGen L C B_strip M₀) (hcR : 0 ≤ cR) (hδ : 0 ≤ δ)
    (hcR_le : cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess P R L N M₀ B_strip)
    (hsin : IntModePrimeSinBound P R L B_sin)
    (hsep : (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cR * apoleBulkConstGen L C B_strip M₀)
    (horth : ∀ ζ ∈ poleOrthSub L M₀,
      (cR + δ) * (ζ ⬝ᵥ ζ) ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))
    (hpole : cA * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀))
    (hcross : ∀ ζ ∈ poleOrthSub L M₀,
      (boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)) ^ 2
        ≤ (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L - cR)
          * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀) * (δ * (ζ ⬝ᵥ ζ)))
    (N : ℕ) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.ApoleMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) :=
  ApoleMat_even_nonneg_of_modeCutoffRung_ApoleHalfMat_bulkStripExcess_primeSin
    hL hb (intModePrimeSinBound_nonneg hsin) hcR hM₀ (hstrip N)
    (modePrimeSinBound_of_intModePrimeSinBound hsin N)
    (fun _ hr => modeCutoffRung_ApoleHalfMat_floor_of_modeBox
      (modeBox_ApoleHalfMat_floor_of_poleOrthSub_A1Mat_only
        hL hcR hδ hcR_le horth hpole hcross) N hr)
    hsep

/-- **Even-sector positivity of `Cvs.Finite.TruncationQuadraticForm.M` for all `N : ℕ` from pure `A1Mat` bounds on `ModeBox M₀`,
`BulkStripExcess`, and `IntModePrimeSinBound`.** -/
theorem M_even_nonneg_of_poleOrthSub_A1Mat_only
    {P R : ℕ} {L : ℝ} (hL : 0 < L) {M₀ : ℕ} {C B_strip B_sin cA cR δ : ℝ}
    (hb : 0 ≤ apoleBulkConstGen L C B_strip M₀) (hcR : 0 ≤ cR) (hδ : 0 ≤ δ)
    (hcR_le : cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
    (hM₀ : L * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess P R L N M₀ B_strip)
    (hsin : IntModePrimeSinBound P R L B_sin)
    (hsep : (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cR * apoleBulkConstGen L C B_strip M₀)
    (horth : ∀ ζ ∈ poleOrthSub L M₀,
      (cR + δ) * (ζ ⬝ᵥ ζ) ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))
    (hpole : cA * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀))
    (hcross : ∀ ζ ∈ poleOrthSub L M₀,
      (boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)) ^ 2
        ≤ (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L - cR)
          * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀) * (δ * (ζ ⬝ᵥ ζ)))
    (N : ℕ) :
    ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := fun ξ hξ =>
  (ApoleMat_even_nonneg_of_poleOrthSub_A1Mat_only
    hL hb hcR hδ hcR_le hM₀ hstrip hsin hsep horth hpole hcross N ξ hξ).trans
    (Cvs.Route.EvenMatrixSlotPoleRestored.ApoleMat_le_M hL P R (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hξ)

/-- **Continuous even window positivity `∀ v ∈ Ev x, 0 ≤ Qx x v` at `x ≥ 2` from pure `A1Mat` bounds
on `ModeBox M₀`, `BulkStripExcess`, and `IntModePrimeSinBound`.** -/
theorem Qx_Ev_nonneg_of_poleOrthSub_A1Mat_only {x : ℕ} (hx : 2 ≤ x)
    {C B_strip B_sin cA cR δ : ℝ} {M₀ : ℕ}
    (hb : 0 ≤ apoleBulkConstGen (Real.log x) C B_strip M₀) (hcR : 0 ≤ cR) (hδ : 0 ≤ δ)
    (hcR_le : cR ≤ cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor (Real.log x) / Real.log x)
    (hM₀ : Real.log x * Real.exp (|C| + 30) ≤ (M₀ : ℝ))
    (hstrip : ∀ N : ℕ, BulkStripExcess x (Nat.clog 2 x) (Real.log x) N M₀ B_strip)
    (hsin : IntModePrimeSinBound x (Nat.clog 2 x) (Real.log x) B_sin)
    (hsep : (B_sin / π) ^ 2 * (4 * (2 * (M₀ : ℝ) + 1))
      ≤ cR * apoleBulkConstGen (Real.log x) C B_strip M₀)
    (horth : ∀ ζ ∈ poleOrthSub (Real.log x) M₀,
      (cR + δ) * (ζ ⬝ᵥ ζ)
        ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ ζ))
    (hpole : cA * (boxPoleVec (Real.log x) M₀ ⬝ᵥ boxPoleVec (Real.log x) M₀)
      ≤ boxPoleVec (Real.log x) M₀
        ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀)
          *ᵥ boxPoleVec (Real.log x) M₀))
    (hcross : ∀ ζ ∈ poleOrthSub (Real.log x) M₀,
      (boxPoleVec (Real.log x) M₀
          ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat x (Nat.clog 2 x) (Real.log x) (boxMode M₀) *ᵥ ζ)) ^ 2
        ≤ (cA + 4 * Cvs.Finite.PairPoleChannelClosed.poleFactor (Real.log x) / Real.log x - cR)
          * (boxPoleVec (Real.log x) M₀ ⬝ᵥ boxPoleVec (Real.log x) M₀) * (δ * (ζ ⬝ᵥ ζ))) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  exact (Cvs.Route.EvenMatrixSlotPoleRestored.Qx_Ev_nonneg_iff_M_even_nonneg hx).2
    (M_even_nonneg_of_poleOrthSub_A1Mat_only
      hL hb hcR hδ hcR_le hM₀ hstrip hsin hsep horth hpole hcross)

/-- **Master `A1Mat`-only reduction for `RiemannHypothesis`**:
combines `poleOrthSub (Real.log x) M₀` and `boxPoleVec` bounds for `A1Mat` with `BulkStripExcess`
and the `N`-independent `IntModePrimeSinBound`. -/
theorem riemannHypothesis_of_poleOrthSub_A1Mat_only
    (h : ∃ᶠ x : ℕ in atTop,
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
              * (boxPoleVec (Real.log x) M₀ ⬝ᵥ boxPoleVec (Real.log x) M₀) * (δ * (ζ ⬝ᵥ ζ))) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_)
  obtain ⟨C, B_strip, B_sin, cA, cR, δ, M₀, hb, hcR, hδ, hcR_le, hM₀, hstrip, hsin,
    hsep, horth, hpole, hcross⟩ := hx
  exact Qx_Ev_nonneg_of_poleOrthSub_A1Mat_only
    hx2 hb hcR hδ hcR_le hM₀ hstrip hsin hsep horth hpole hcross

end Cvs.Route.PoleOrthPrimeSinReduction
