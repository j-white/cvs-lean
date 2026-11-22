import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.HalfPoleMatrixModeBox
import Cvs.Route.HighModePoleTailDecay
import Cvs.Route.LadderFreePrimeTailCoupling
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PosChannelFloorCoercivity

/-!
# Codimension-1 Pole-Orthogonal Subspace `poleOrthSub` on `ModeBox M₀`

Splits `evenModeSub (negBox M₀)` orthogonally along `boxPoleVec L M₀` and `poleOrthSub L M₀`, where
`poleRankOneMat` vanishes identically and `ApoleHalfMat` reduces to `A1Mat`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PoleOrthogonalSubspace
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

/-! ### The pole vector `boxPoleVec` and zero-mode element `zeroBox` on `ModeBox M₀` -/

/-- **The pole evaluation vector on `ModeBox M₀`**:
`boxPoleVec L M₀ m = uu (1 / 2) (2π m / L)`. -/
def boxPoleVec (L : ℝ) (M₀ : ℕ) : ModeBox M₀ → ℝ :=
  poleVec L (boxMode M₀)

/-- **The zero mode `0 ∈ ModeBox M₀`.** -/
def zeroBox (M₀ : ℕ) : ModeBox M₀ :=
  ⟨0, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩

/-- `boxMode M₀ (zeroBox M₀) = 0`. -/
theorem boxMode_zeroBox (M₀ : ℕ) : boxMode M₀ (zeroBox M₀) = 0 := rfl

/-- At `zeroBox M₀`, `boxPoleVec L M₀ (zeroBox M₀) = 2`. -/
theorem boxPoleVec_zeroBox (L : ℝ) (M₀ : ℕ) :
    boxPoleVec L M₀ (zeroBox M₀) = 2 := by
  unfold boxPoleVec poleVec
  rw [boxMode_zeroBox, Int.cast_zero, mul_zero, zero_div, Cvs.Route.PosChannelFloorCoercivity.uu_half_zero]

/-- `boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ ≥ 4` for all `L : ℝ` and `M₀ : ℕ`. -/
theorem four_le_boxPoleVec_dotProduct_self (L : ℝ) (M₀ : ℕ) :
    4 ≤ boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ := by
  have hle : boxPoleVec L M₀ (zeroBox M₀) * boxPoleVec L M₀ (zeroBox M₀)
      ≤ ∑ m : ModeBox M₀, boxPoleVec L M₀ m * boxPoleVec L M₀ m :=
    Finset.single_le_sum (fun m _ => mul_self_nonneg (boxPoleVec L M₀ m))
      (Finset.mem_univ (zeroBox M₀))
  rw [boxPoleVec_zeroBox] at hle
  change 4 ≤ ∑ m : ModeBox M₀, boxPoleVec L M₀ m * boxPoleVec L M₀ m
  linarith

/-- `boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ > 0` for all `L : ℝ` and `M₀ : ℕ`. -/
theorem boxPoleVec_dotProduct_self_pos (L : ℝ) (M₀ : ℕ) :
    0 < boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ := by
  linarith [four_le_boxPoleVec_dotProduct_self L M₀]

/-- `boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ ≠ 0`. -/
theorem boxPoleVec_dotProduct_self_ne_zero (L : ℝ) (M₀ : ℕ) :
    boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀ ≠ 0 :=
  (boxPoleVec_dotProduct_self_pos L M₀).ne'

/-- `Cvs.Finite.WindowMatrixSymbolKernel.uu a` is an even function of `ω`. -/
theorem uu_neg (a ω : ℝ) : Cvs.Finite.WindowMatrixSymbolKernel.uu a (-ω) = Cvs.Finite.WindowMatrixSymbolKernel.uu a ω := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
  rw [neg_sq]

/-- `boxPoleVec L M₀` belongs to the even subspace `evenModeSub (negBox M₀)`. -/
theorem boxPoleVec_mem_evenModeSub (L : ℝ) (M₀ : ℕ) :
    boxPoleVec L M₀ ∈ evenModeSub (negBox M₀) := by
  intro m
  unfold boxPoleVec poleVec
  rw [boxMode_negBox, Int.cast_neg]
  have hneg : 2 * π * -(boxMode M₀ m : ℝ) / L = -(2 * π * (boxMode M₀ m : ℝ) / L) := by ring
  rw [hneg, uu_neg]

/-! ### The codimension-1 pole-orthogonal subspace `poleOrthSub` and orthogonal projection -/

/-- **The codimension-1 pole-orthogonal even subspace of `ModeBox M₀`**:
even vectors on `ModeBox M₀` orthogonal to `boxPoleVec L M₀`. -/
def poleOrthSub (L : ℝ) (M₀ : ℕ) : Submodule ℝ (ModeBox M₀ → ℝ) where
  carrier := {η | η ∈ evenModeSub (negBox M₀) ∧ boxPoleVec L M₀ ⬝ᵥ η = 0}
  add_mem' ha hb :=
    ⟨(evenModeSub (negBox M₀)).add_mem ha.1 hb.1,
      by rw [dotProduct_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨(evenModeSub (negBox M₀)).zero_mem, dotProduct_zero _⟩
  smul_mem' c _ ha :=
    ⟨(evenModeSub (negBox M₀)).smul_mem c ha.1,
      by rw [dotProduct_smul, ha.2, smul_zero]⟩

/-- **The pole-component coefficient** of `η : ModeBox M₀ → ℝ` along `boxPoleVec L M₀`. -/
def poleCoeff (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ℝ :=
  (boxPoleVec L M₀ ⬝ᵥ η) / (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)

/-- **The orthogonal projection of `η` onto the complement of `boxPoleVec L M₀`.** -/
def poleOrthProj (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) : ModeBox M₀ → ℝ :=
  η - poleCoeff L M₀ η • boxPoleVec L M₀

/-- `poleOrthProj L M₀ η` is orthogonal to `boxPoleVec L M₀`. -/
theorem boxPoleVec_dotProduct_poleOrthProj (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    boxPoleVec L M₀ ⬝ᵥ poleOrthProj L M₀ η = 0 := by
  unfold poleOrthProj poleCoeff
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul,
    div_mul_cancel₀ _ (boxPoleVec_dotProduct_self_ne_zero L M₀), sub_self]

/-- If `η ∈ evenModeSub (negBox M₀)`, then `poleOrthProj L M₀ η ∈ poleOrthSub L M₀`. -/
theorem poleOrthProj_mem_poleOrthSub (L : ℝ) (M₀ : ℕ) {η : ModeBox M₀ → ℝ}
    (hη : η ∈ evenModeSub (negBox M₀)) :
    poleOrthProj L M₀ η ∈ poleOrthSub L M₀ :=
  ⟨(evenModeSub (negBox M₀)).sub_mem hη
      ((evenModeSub (negBox M₀)).smul_mem _ (boxPoleVec_mem_evenModeSub L M₀)),
    boxPoleVec_dotProduct_poleOrthProj L M₀ η⟩

/-- Orthogonal decomposition `η = poleCoeff L M₀ η • boxPoleVec L M₀ + poleOrthProj L M₀ η`. -/
theorem eq_smul_boxPoleVec_add_poleOrthProj (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η = poleCoeff L M₀ η • boxPoleVec L M₀ + poleOrthProj L M₀ η := by
  unfold poleOrthProj
  abel

/-- Pythagorean identity for the orthogonal decomposition along `boxPoleVec L M₀`:
`η ⬝ᵥ η = (poleCoeff L M₀ η)² * (boxPoleVec ⬝ᵥ boxPoleVec) + poleOrthProj η ⬝ᵥ poleOrthProj η`. -/
theorem dotProduct_self_eq_poleCoeff_sq_add_poleOrthProj (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ η = (poleCoeff L M₀ η) ^ 2 * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      + poleOrthProj L M₀ η ⬝ᵥ poleOrthProj L M₀ η := by
  conv_lhs => rw [eq_smul_boxPoleVec_add_poleOrthProj L M₀ η]
  have horth1 : boxPoleVec L M₀ ⬝ᵥ poleOrthProj L M₀ η = 0 :=
    boxPoleVec_dotProduct_poleOrthProj L M₀ η
  have horth2 : poleOrthProj L M₀ η ⬝ᵥ boxPoleVec L M₀ = 0 := by
    rw [dotProduct_comm, horth1]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    horth1, horth2, mul_zero, add_zero, zero_add]
  ring

/-! ### Vanishing of `poleRankOneMat` on `poleOrthSub` and `ApoleHalfMat` decomposition -/

/-- `poleRankOneMat L (boxMode M₀) *ᵥ poleOrthProj L M₀ η = 0` for every `η : ModeBox M₀ → ℝ`. -/
theorem poleRankOneMat_mulVec_poleOrthProj (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    poleRankOneMat L (boxMode M₀) *ᵥ poleOrthProj L M₀ η = 0 := by
  ext m
  rw [poleRankOneMat_mulVec]
  change (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L) * boxPoleVec L M₀ m
    * (boxPoleVec L M₀ ⬝ᵥ poleOrthProj L M₀ η) = 0
  rw [boxPoleVec_dotProduct_poleOrthProj, mul_zero]

/-- `ApoleHalfMat *ᵥ poleOrthProj L M₀ η = A1Mat *ᵥ poleOrthProj L M₀ η` for all `η : ModeBox M₀ → ℝ`. -/
theorem ApoleHalfMat_mulVec_poleOrthProj (P R : ℕ) (L : ℝ) (M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    ApoleHalfMat P R L (boxMode M₀) *ᵥ poleOrthProj L M₀ η
      = Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ poleOrthProj L M₀ η := by
  simp [ApoleHalfMat, Matrix.add_mulVec, Matrix.smul_mulVec,
    poleRankOneMat_mulVec_poleOrthProj]

/-- **Exact quadratic decomposition of `ApoleHalfMat` along `boxPoleVec` and `poleOrthProj`**:
`poleRankOneMat` contributes purely to the `1 × 1` `boxPoleVec` block, while the cross-term and
codimension-1 block involve only `A1Mat`. -/
theorem ApoleHalfMat_quad_decomp (P R : ℕ) {L : ℝ} (hL : 0 < L) (M₀ : ℕ)
    (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ η)
      = (poleCoeff L M₀ η) ^ 2
          * (boxPoleVec L M₀ ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀))
        + 2 * poleCoeff L M₀ η
          * (boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ poleOrthProj L M₀ η))
        + poleOrthProj L M₀ η ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ poleOrthProj L M₀ η) := by
  conv_lhs => rw [eq_smul_boxPoleVec_add_poleOrthProj L M₀ η]
  have hsym : poleOrthProj L M₀ η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀)
      = boxPoleVec L M₀ ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ poleOrthProj L M₀ η) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (ApoleHalfMat_boxMode_isSymm hL P R M₀).eq, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hsym,
    ApoleHalfMat_mulVec_poleOrthProj P R L M₀ η]
  ring

/-! ### Reduction of the `ModeBox M₀` floor of `ApoleHalfMat` and `RiemannHypothesis` to `poleOrthSub` -/

/-- **Reduction of the `ModeBox M₀` floor of `ApoleHalfMat` to an `A1Mat` floor `cR + δ` on the
codimension-1 subspace `poleOrthSub L M₀`.** -/
theorem modeBox_ApoleHalfMat_floor_of_poleOrthSub_A1Mat_floor
    {P R M₀ : ℕ} {L cR δ : ℝ} (hL : 0 < L) (hcR : 0 ≤ cR) (hδ : 0 ≤ δ)
    (h_orth : ∀ ζ ∈ poleOrthSub L M₀,
      (cR + δ) * (ζ ⬝ᵥ ζ) ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))
    (h_pole : cR * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀)
      ≤ boxPoleVec L M₀ ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀))
    (h_cross : ∀ ζ ∈ poleOrthSub L M₀,
      (boxPoleVec L M₀ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)) ^ 2
        ≤ (boxPoleVec L M₀ ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ boxPoleVec L M₀)
            - cR * (boxPoleVec L M₀ ⬝ᵥ boxPoleVec L M₀))
          * (δ * (ζ ⬝ᵥ ζ)))
    (η : ModeBox M₀ → ℝ) (hη : η ∈ evenModeSub (negBox M₀)) :
    cR * (η ⬝ᵥ η) ≤ η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ η) := by
  have _ := hcR
  set c := poleCoeff L M₀ η
  set u := boxPoleVec L M₀
  set ζ := poleOrthProj L M₀ η
  have hζ : ζ ∈ poleOrthSub L M₀ := poleOrthProj_mem_poleOrthSub L M₀ hη
  have hdecomp : η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ η)
      = c ^ 2 * (u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u))
        + 2 * c * (u ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))
        + ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ) :=
    ApoleHalfMat_quad_decomp P R hL M₀ η
  have hnorm : η ⬝ᵥ η = c ^ 2 * (u ⬝ᵥ u) + (ζ ⬝ᵥ ζ) :=
    dotProduct_self_eq_poleCoeff_sq_add_poleOrthProj L M₀ η
  have hid : η ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ η) - cR * (η ⬝ᵥ η)
      = c ^ 2 * (u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u) - cR * (u ⬝ᵥ u))
        + 2 * (c * (u ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)))
        + (ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ) - cR * (ζ ⬝ᵥ ζ)) := by
    rw [hdecomp, hnorm]
    ring
  have horth_ζ : δ * (ζ ⬝ᵥ ζ) ≤ ζ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ) - cR * (ζ ⬝ᵥ ζ) := by
    linarith [h_orth ζ hζ]
  have hcross_ζ := h_cross ζ hζ
  have hA : 0 ≤ c ^ 2 * (u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u) - cR * (u ⬝ᵥ u)) :=
    mul_nonneg (sq_nonneg c) (sub_nonneg.2 h_pole)
  have hC : 0 ≤ δ * (ζ ⬝ᵥ ζ) := mul_nonneg hδ (Cvs.Route.PoleSlotRungResidual.dotProduct_self_nonneg ζ)
  have hB : (c * (u ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))) ^ 2
      ≤ (c ^ 2 * (u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u) - cR * (u ⬝ᵥ u)))
        * (δ * (ζ ⬝ᵥ ζ)) := by
    have hmul := mul_le_mul_of_nonneg_left hcross_ζ (sq_nonneg c)
    linarith [show (c * (u ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ))) ^ 2
      = c ^ 2 * (u ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ ζ)) ^ 2 by ring,
      show c ^ 2 * ((u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u) - cR * (u ⬝ᵥ u)) * (δ * (ζ ⬝ᵥ ζ)))
      = (c ^ 2 * (u ⬝ᵥ (ApoleHalfMat P R L (boxMode M₀) *ᵥ u) - cR * (u ⬝ᵥ u))) * (δ * (ζ ⬝ᵥ ζ)) by ring]
  have hquad := Cvs.Route.PoleSlotRungResidual.quad_nonneg_of_sq_le hA hC hB
  linarith

end Cvs.Route.PoleOrthogonalSubspace
