import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.LevyExpMoments
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxFourChannelLevy
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.TruncatedArchChannelSum
import Cvs.Zeta.Digamma

/-!
# Multi-Channel Green-Laplace Identity and Four-Channel Decomposition on `ModeBox M₀`

Proves the Laplace identity `greenChannelEntry L k m n = 2 uu(b_k) δ_{mn} - atom L k / L` for every
Lévy channel `k` and lifts the resulting 4-channel matrix decomposition to `ModeBox M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxGreenLaplace
open Cvs.ZeroCounting

open scoped BigOperators Matrix InnerProductSpace
open Real Set MeasureTheory Filter Finset
open Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
open Cvs.WeilForm.Archimedean.OffWindowDefect
open Cvs.WeilForm.Archimedean.TruncationBelowSymbol
open Cvs.Finite.SymmetricModeSet
open Cvs.Finite.WindowMatrixSymbolKernel
open Cvs.WeilForm.EvenBoundaryKernelBound
open Cvs.WeilForm.GreenRemovesFirstArchChannel
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxShiftedArchGreen
open Cvs.Route.ModeBoxFourChannelLevy

/-! ### General `k`-th channel Green-Laplace pairing `greenChannelEntry` -/

/-- The `k`-th channel exponential Laplace pairing of the cut cosine kernel `Cvs.Finite.LevyKernelIncrement.Kc`. -/
def greenChannelEntry (L : ℝ) (k : ℕ) (m n : ℤ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * Cvs.Finite.LevyKernelIncrement.Kc L m n v

/-- **Exact Laplace-moment identity for the `k`-th channel**: generalizes
`Cvs.WeilForm.ArchGreenSecondChannel.greenEntry_eq_first_moment` from `k = 0` to arbitrary `k : ℕ`. -/
theorem greenChannelEntry_eq_moment {L : ℝ} (hL : 0 < L) (k : ℕ) (m n : ℤ) :
    greenChannelEntry L k m n =
      (1 / Cvs.Finite.WindowMatrixSymbolKernel.bk k) * Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.LevyExpMoments.moment L m n k / 2 := by
  let g := fun v => Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * (Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n v)
  have hi1 : IntegrableOn (fun v => Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * Cvs.Finite.CosineModeOverlap.K L m n 0)
      (Ioi 0) volume := by
    change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (by nlinarith [Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k] : -Cvs.Finite.WindowMatrixSymbolKernel.bk k < 0) 0).mul_const
        (Cvs.Finite.CosineModeOverlap.K L m n 0)
  have hi2 : IntegrableOn (fun v => Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * Cvs.Finite.LevyKernelIncrement.Kc L m n v)
      (Ioi 0) volume := by
    simpa only [neg_mul] using Cvs.Finite.ModeSumPairValues.integrableOn_exp_mul_Kc hL m n (-Cvs.Finite.WindowMatrixSymbolKernel.bk k)
  have hm : Cvs.Finite.LevyExpMoments.moment L m n k = 2 * ∫ v in Ioi (0 : ℝ), g v := by
    unfold Cvs.Finite.LevyExpMoments.moment
    have hs := integral_comp_mul_left_Ioi'
      (fun u => Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2)))
      0 (show (0 : ℝ) < 2 by norm_num)
    rw [mul_zero, smul_eq_mul] at hs
    rw [← hs]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    simp only [g, Cvs.Finite.WindowMatrixSymbolKernel.bk]
    rw [show 2 * v / 2 = v by ring]
    congr 2
    ring
  have hs : (∫ v in Ioi (0 : ℝ), g v) =
      (1 / Cvs.Finite.WindowMatrixSymbolKernel.bk k) * Cvs.Finite.CosineModeOverlap.K L m n 0 - greenChannelEntry L k m n := by
    have he : g = (fun v => Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * Cvs.Finite.CosineModeOverlap.K L m n 0) -
        (fun v => Real.exp (-(Cvs.Finite.WindowMatrixSymbolKernel.bk k * v)) * Cvs.Finite.LevyKernelIncrement.Kc L m n v) := by
      funext v; dsimp [g]; ring
    rw [he]
    simp only [Pi.sub_apply]
    rw [integral_sub hi1 hi2, integral_mul_const,
      Cvs.WeilForm.TruncatedArchChannelSum.integral_exp_neg_scaled (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k)]
    rfl
  rw [hs] at hm
  linarith

/-- **Exact spectral-atom decomposition of `greenChannelEntry L k m n`**: equals the `k`-th
Lorentzian diagonal `2 * uu (bk k)` minus the `k`-th boundary atom `atom L k / L`. -/
theorem greenChannelEntry_eq {L : ℝ} (hL : 0 < L) (k : ℕ) (m n : ℤ) :
    greenChannelEntry L k m n =
      (if m = n then 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * m / L) else 0) -
        Cvs.WeilForm.ArchGreenSecondChannel.atom L k (2 * π * m / L) (2 * π * n / L) / L := by
  rw [greenChannelEntry_eq_moment hL, Cvs.WeilForm.ArchGreenSecondChannel.moment_eq_deficit_atom hL]
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, if_pos rfl]
    have hd := Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit (2 * π * m / L) k
    rw [two_mul_bIdx_div_eq_two_mul_uu k (2 * π * m / L)] at hd
    rw [Cvs.Finite.CosineModeOverlap.K, if_pos rfl]
    simp only [mul_zero, zero_div, sub_zero, Real.cos_zero, mul_one]
    have hbk : (1 / Cvs.Finite.WindowMatrixSymbolKernel.bk k) * 2 = 1 / ((k : ℝ) + 1 / 4) := by
      unfold Cvs.Finite.WindowMatrixSymbolKernel.bk
      have hb : 2 * (k : ℝ) + 1 / 2 ≠ 0 := (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k).ne'
      have hk : (k : ℝ) + 1 / 4 ≠ 0 := by positivity
      field_simp
      ring
    linarith
  · rw [if_neg hmn, if_neg hmn, Cvs.Finite.CosineModeOverlap.K, if_neg hmn]
    simp only [mul_zero, Real.sin_zero, sub_self, zero_div, zero_sub, zero_add]

/-! ### Higher-channel boundary tail `boundaryTailFrom N` and finite-channel splitting -/

/-- The Archimedean boundary ladder starting at channel `N`. -/
def boundaryTailFrom (N : ℕ) (L A B : ℝ) : ℝ :=
  ∑' k : ℕ, Cvs.WeilForm.ArchGreenSecondChannel.atom L (k + N) A B

/-- **Finite-channel splitting of `Cvs.WeilForm.ArchGreenSecondChannel.boundaryTail`** into `Finset.Ico 1 N` plus
`boundaryTailFrom N` for `1 ≤ N`. -/
theorem boundaryTail_eq_sum_Ico_add_boundaryTailFrom
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) (A B : ℝ) :
    Cvs.WeilForm.ArchGreenSecondChannel.boundaryTail L A B =
      (∑ k ∈ Finset.Ico 1 N, Cvs.WeilForm.ArchGreenSecondChannel.atom L k A B) + boundaryTailFrom N L A B := by
  have hfull := Cvs.WeilForm.ArchGreenSecondChannel.full_boundary_eq hL A B
  have hNsum : (∑ k ∈ Finset.range N, Cvs.WeilForm.ArchGreenSecondChannel.atom L k A B) + boundaryTailFrom N L A B =
      ∑' k : ℕ, Cvs.WeilForm.ArchGreenSecondChannel.atom L k A B :=
    (Cvs.WeilForm.ArchGreenSecondChannel.summable_atom hL A B).sum_add_tsum_nat_add N
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => Cvs.WeilForm.ArchGreenSecondChannel.atom L k A B) hN
  rw [Finset.sum_range_one] at hsplit
  linarith

/-- Rank-two square decomposition of `boundaryTailFrom N` on any finite index type. -/
theorem boundaryTailFrom_quad {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (N : ℕ) (ω : ι → ℝ) (ξ : ι → ℝ) :
    (∑ i, ∑ j, ξ i * ξ j * boundaryTailFrom N L (ω i) (ω j)) =
      ∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k + N) *
        ((∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk (k + N)) (ω i)) ^ 2 -
          (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.vv (Cvs.Finite.WindowMatrixSymbolKernel.bk (k + N)) (ω i)) ^ 2) := by
  have hs : ∀ i j, Summable (fun k : ℕ => ξ i * ξ j * Cvs.WeilForm.ArchGreenSecondChannel.atom L (k + N) (ω i) (ω j)) :=
    fun i j => ((Cvs.WeilForm.ArchGreenSecondChannel.summable_atom hL (ω i) (ω j)).comp_injective
      (add_left_injective N)).mul_left _
  unfold boundaryTailFrom
  simp_rw [← tsum_mul_left]
  have h2 : ∀ i, (∑ j, ∑' k : ℕ, ξ i * ξ j * Cvs.WeilForm.ArchGreenSecondChannel.atom L (k + N) (ω i) (ω j)) =
      ∑' k : ℕ, ∑ j, ξ i * ξ j * Cvs.WeilForm.ArchGreenSecondChannel.atom L (k + N) (ω i) (ω j) :=
    fun i => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  simp only [h2]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  exact tsum_congr fun k => Cvs.Finite.WindowMatrixSymbolKernel.rank2_quad _ _ _ _

/-- Even-sector sum-of-squares identity for `boundaryTailFrom N`. -/
theorem boundaryTailFrom_quad_even {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (N : ℕ) (ω : ι → ℝ) (ξ : ι → ℝ)
    (hv : ∀ b : ℝ, 0 < b → ∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.vv b (ω i) = 0) :
    (∑ i, ∑ j, ξ i * ξ j * boundaryTailFrom N L (ω i) (ω j)) =
      ∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k + N) *
        (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk (k + N)) (ω i)) ^ 2 := by
  rw [boundaryTailFrom_quad hL N ω ξ]
  simp only [hv _ (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos _), zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]

/-- Nonnegativity of `boundaryTailFrom N` when the odd boundary pairings vanish. -/
theorem boundaryTailFrom_quad_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (N : ℕ) (ω : ι → ℝ) (ξ : ι → ℝ)
    (hv : ∀ b : ℝ, 0 < b → ∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.vv b (ω i) = 0) :
    0 ≤ ∑ i, ∑ j, ξ i * ξ j * boundaryTailFrom N L (ω i) (ω j) := by
  rw [boundaryTailFrom_quad_even hL N ω ξ hv]
  exact tsum_nonneg fun k => mul_nonneg (Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL _) (sq_nonneg _)

/-! ### Lifting `greenChannelEntry` and `boundaryTailFrom` to `ModeBox M₀` -/

/-- The `k`-th channel Green-Laplace matrix on `ModeBox M₀`. -/
def boxGreenChannelMatrix (L : ℝ) (k : ℕ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun i j => greenChannelEntry L k (boxMode M₀ i) (boxMode M₀ j)

/-- The higher-channel boundary tail matrix `boundaryTailFrom N / L` on `ModeBox M₀`. -/
def boxTailMatrixFrom (N : ℕ) (L : ℝ) (M₀ : ℕ) : Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun i j =>
    boundaryTailFrom N L (2 * π * (boxMode M₀ i : ℝ) / L)
      (2 * π * (boxMode M₀ j : ℝ) / L) / L

/-- **On `evenModeSub (negBox M₀)`, `boxTailMatrixFrom N` is positive semidefinite.** -/
theorem boxTailMatrixFrom_quad_nonneg {L : ℝ} (hL : 0 < L) (N M₀ : ℕ)
    {η : ModeBox M₀ → ℝ} (hη : η ∈ evenModeSub (negBox M₀)) :
    0 ≤ η ⬝ᵥ (boxTailMatrixFrom N L M₀ *ᵥ η) := by
  have heq : η ⬝ᵥ (boxTailMatrixFrom N L M₀ *ᵥ η) =
      (∑ m : ModeBox M₀, ∑ n : ModeBox M₀, η m * η n *
        boundaryTailFrom N L (2 * π * (boxMode M₀ m : ℝ) / L)
          (2 * π * (boxMode M₀ n : ℝ) / L)) / L := by
    simp only [dotProduct, Matrix.mulVec, boxTailMatrixFrom, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [heq]
  exact div_nonneg (boundaryTailFrom_quad_nonneg hL N
    (fun m => 2 * π * (boxMode M₀ m : ℝ) / L) η
    (fun b _ => box_sum_even_mul_vv_eq_zero L b hη)) hL.le

/-- Entrywise identity for the sum of `boxGreenChannelMatrix L k M₀` over `k ∈ Finset.Ico 1 4`. -/
theorem sum_Ico_boxGreenChannelMatrix_apply {L : ℝ} (hL : 0 < L) (M₀ : ℕ)
    (i j : ModeBox M₀) :
    (∑ k ∈ Finset.Ico 1 4, boxGreenChannelMatrix L k M₀ i j) =
      (if i = j then
        ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ i : ℝ) / L)
      else 0) -
        (boxTailMatrix L M₀ i j - boxTailMatrixFrom 4 L M₀ i j) := by
  have h1 : ∀ k ∈ Finset.Ico 1 4, boxGreenChannelMatrix L k M₀ i j =
      (if i = j then 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ i : ℝ) / L) else 0) -
        Cvs.WeilForm.ArchGreenSecondChannel.atom L k (2 * π * (boxMode M₀ i : ℝ) / L)
          (2 * π * (boxMode M₀ j : ℝ) / L) / L := by
    intro k _
    dsimp [boxGreenChannelMatrix]
    simp only [greenChannelEntry_eq hL k (boxMode M₀ i) (boxMode M₀ j),
      (boxMode_injective M₀).eq_iff]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hdiag : (∑ k ∈ Finset.Ico 1 4,
      if i = j then 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ i : ℝ) / L) else 0) =
      if i = j then
        ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ i : ℝ) / L)
      else 0 := by
    by_cases hij : i = j <;> simp [hij]
  have htail := boundaryTail_eq_sum_Ico_add_boundaryTailFrom hL 4 (by decide)
    (2 * π * (boxMode M₀ i : ℝ) / L) (2 * π * (boxMode M₀ j : ℝ) / L)
  rw [hdiag]
  dsimp [boxTailMatrix, boxTailMatrixFrom]
  rw [htail, add_div]
  ring

/-- **Exact quadratic form identity for the intermediate Green channels `k = 1, 2, 3`**:
connects `∑_{k=1}^3 ηᵀ G_k η` to `boxResidualLevyDiagQ` and the boundary tail difference. -/
theorem sum_Ico_boxGreenChannelMatrix_quad_eq {L : ℝ} (hL : 0 < L) (M₀ : ℕ)
    (η : ModeBox M₀ → ℝ) :
    (∑ k ∈ Finset.Ico 1 4, η ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ η)) =
      boxResidualLevyDiagQ L M₀ η -
        (η ⬝ᵥ (boxTailMatrix L M₀ *ᵥ η) - η ⬝ᵥ (boxTailMatrixFrom 4 L M₀ *ᵥ η)) := by
  have hcomm : (∑ k ∈ Finset.Ico 1 4, η ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ η)) =
      ∑ i : ModeBox M₀, ∑ j : ModeBox M₀,
        η i * η j * (∑ k ∈ Finset.Ico 1 4, boxGreenChannelMatrix L k M₀ i j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  rw [hcomm]
  simp only [sum_Ico_boxGreenChannelMatrix_apply hL M₀, mul_sub, Finset.sum_sub_distrib]
  have hdiag : (∑ i : ModeBox M₀, ∑ j : ModeBox M₀, η i * η j *
      (if i = j then
        ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * (boxMode M₀ i : ℝ) / L)
      else 0)) = boxResidualLevyDiagQ L M₀ η := by
    unfold boxResidualLevyDiagQ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [Ne.symm hji]) (by simp)]
    simp only [↓reduceIte]
    ring
  have hT1 : (∑ i : ModeBox M₀, ∑ j : ModeBox M₀, η i * η j * boxTailMatrix L M₀ i j) =
      η ⬝ᵥ (boxTailMatrix L M₀ *ᵥ η) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2 : (∑ i : ModeBox M₀, ∑ j : ModeBox M₀, η i * η j * boxTailMatrixFrom 4 L M₀ i j) =
      η ⬝ᵥ (boxTailMatrixFrom 4 L M₀ *ᵥ η) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag, hT1, hT2]

/-- **Exact four-channel quadratic form identity for `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀`**:
absorbs the three intermediate Lévy channels `k = 1, 2, 3` into `boxMultiShiftedDiag 4`
and `boxTailMatrixFrom 4` minus the three Green-Laplace matrices `boxGreenChannelMatrix L k M₀`. -/
theorem boxM_quad_eq_multi_four_add_tailFrom_sub_green_sub_discrepancy
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ) (η : ModeBox M₀ → ℝ) :
    η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η) =
      η ⬝ᵥ (boxMultiShiftedDiag 4 L M₀ *ᵥ η) + η ⬝ᵥ (boxTailMatrixFrom 4 L M₀ *ᵥ η) -
        (∑ k ∈ Finset.Ico 1 4, η ⬝ᵥ (boxGreenChannelMatrix L k M₀ *ᵥ η)) -
        η ⬝ᵥ (boxDiscrepancyMatrix P R L M₀ *ᵥ η) := by
  have h1 := boxM_quad_eq_shifted hL P R M₀ η
  rw [boxArchGreenMatrix, Matrix.add_mulVec, dotProduct_add,
    boxShiftedDiag_quad_eq_multi_four_sub_residual L M₀ η] at h1
  have h2 := sum_Ico_boxGreenChannelMatrix_quad_eq hL M₀ η
  linarith

end Cvs.Route.ModeBoxGreenLaplace
