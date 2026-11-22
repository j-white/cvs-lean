import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.BoundaryStripFolding
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.HighModeTailArchFree
import Cvs.Route.PoleMatChannelStrip
import Cvs.Route.PoleMatDefiniteSign
import Cvs.Route.PoleSlotRungResidual
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Ladder-Free `A1Mat` and `ApoleMat` Reductions and Pure `kPrimeMat` Tail Coupling

Decouples the digamma ladder before the rung-bulk split so high-mode off-diagonal coupling
is driven purely by `kPrimeMat` (for `A1Mat`) or `poleRankOneMat + kPrimeMat` (for `ApoleMat`).
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.LadderFreePrimeTailCoupling
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
open Cvs.Route.HighModeTailArchFree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Explicit `kPrimeMat` and `poleRankOneMat` decompositions of `A1Mat` and `ApoleMat` -/

/-- **The finite prime kernel matrix** `kPrimeMat P R L mode`:
`(kPrimeMat P R L mode)_{i,j} = (1 / L) * kPrime P R L ω_i ω_j`. -/
def kPrimeMat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * mode i / L) (2 * π * mode j / L)

/-- **The rank-one pole matrix** `poleRankOneMat L mode`:
`(poleRankOneMat L mode)_{i,j} = (2 * poleFactor L / L) * uu(1/2, ω_i) * uu(1/2, ω_j)`. -/
def poleRankOneMat (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j =>
    (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
      * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L) * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode j / L)

/-- **For `0 < L` and injective `mode`, `A1Mat = symbolDiagMat + kPrimeMat`** (completely free of
both the pole and the infinite digamma ladder). -/
theorem A1Mat_eq_symbolDiagMat_add_kPrimeMat {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) :
    Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode = symbolDiagMat P R L mode + kPrimeMat P R L mode := by
  ext i j
  simp only [Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat, symbolDiagMat, kPrimeMat, Matrix.add_apply,
    Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R hinj i j, Cvs.Finite.WindowMatrixSymbolKernel.kK]
  ring

omit [Fintype ι] in
/-- `ApoleMat` is `A1Mat + poleRankOneMat`. -/
theorem ApoleMat_eq_A1Mat_add_poleRankOneMat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) :
    ApoleMat P R L mode = Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode + poleRankOneMat L mode := by
  ext i j
  rfl

/-! ### Quadratic form and unconditional bulk floor of `A1Mat` on `lowModeRung` -/

/-- **Exact quadratic form decomposition of `A1Mat`**:
`ξ ⬝ᵥ (A1Mat *ᵥ ξ) = (∑_i ξ_i² archSymbol(ω_i)) + sinStripQ ξ − cosStripQ ξ`. -/
theorem A1Mat_quad_eq_archSymbol_add_sinStripQ_sub_cosStripQ {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ ξ)
      = (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
        + sinStripQ P R L mode ξ - cosStripQ P R L mode ξ := by
  have h1 := Cvs.Route.EvenMatrixSlotPoleRestored.quad_ApoleMat_eq P R L mode ξ
  have h2 := Cvs.Route.PoleMatChannelStrip.ApoleMat_quad_eq_posChannelQ_sub_cosStripQ hL P R hinj ξ
  rw [Cvs.Route.BoundaryStripFolding.posChannelQ_eq_archPoleQ_add_sinStripQ, Cvs.Route.BoundaryStripFolding.archPoleQ] at h2
  linarith

/-! ### Symmetry and high-mode tail decoupling for `A1Mat` and `ApoleMat` -/

/-- `A1Mat P R L (mode N)` is symmetric for `0 < L`. -/
theorem A1Mat_isSymm {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N)).IsSymm :=
  Cvs.Route.PoleMatDefiniteSign.A1Mat_isSymm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)

/-- **For `0 < L`, injective `mode`, `r ∈ Submodule.span ℝ (evenBasisVec neg '' S)` (with `S`
`neg`-invariant), and `i ∉ S`, `evenProjVec neg (A1Mat *ᵥ r) i = evenProjVec neg (kPrimeMat *ᵥ r) i`.** -/
theorem evenProjVec_A1Mat_mulVec_eq_kPrimeMat_of_not_mem {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode)
    {S : Set ι} {neg : ι → ι} (hS : ∀ j, neg j ∈ S ↔ j ∈ S)
    {r : ι → ℝ} (hr : r ∈ Submodule.span ℝ (evenBasisVec neg '' S))
    {i : ι} (hi : i ∉ S) :
    evenProjVec neg (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode *ᵥ r) i
      = evenProjVec neg (kPrimeMat P R L mode *ᵥ r) i := by
  have hni : neg i ∉ S := fun h => hi ((hS i).1 h)
  have h1 := symbolDiagMat_mulVec_apply_eq_zero_of_not_mem P R L mode hS hr hi
  have h2 := symbolDiagMat_mulVec_apply_eq_zero_of_not_mem P R L mode hS hr hni
  rw [A1Mat_eq_symbolDiagMat_add_kPrimeMat hL P R hinj, Matrix.add_mulVec]
  simp [evenProjVec, h1, h2]

/-- **Exact `kPrimeMat` high-mode tail formula for the `A1Mat` rung residual** on any `negI N`-invariant
mode set `S`. -/
theorem exists_A1Mat_residual_eq_kPrime_tail {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)]
    (hS : ∀ i, Cvs.Finite.SymmetricModeSet.negI N i ∈ S ↔ i ∈ S)
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ Submodule.span ℝ (evenBasisVec (Cvs.Finite.SymmetricModeSet.negI N) '' S)) :
    ∃ z ∈ Submodule.span ℝ (evenBasisVec (Cvs.Finite.SymmetricModeSet.negI N) '' S),
      ((evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) - z)
        ⬝ᵥ (evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) - z))
        = ∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
            if i ∉ S then
              (evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (kPrimeMat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) i) ^ 2
            else 0 := by
  set v := evenProjVec (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
  have hv : v ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N) :=
    evenProjVec_mem_evenModeSub (Cvs.Finite.SymmetricModeSet.negI_involutive N) _
  refine ⟨restrictVec S v,
    restrictVec_mem_span_evenBasisVec S (Cvs.Finite.SymmetricModeSet.negI_involutive N) hS hv, ?_⟩
  rw [← complVec_eq_sub_restrictVec S v, complVec_dotProduct_self S v]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, not_false_eq_true, ↓reduceIte, v]
    rw [evenProjVec_A1Mat_mulVec_eq_kPrimeMat_of_not_mem hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) hS hr hi]

/-! ### General self-slot positivity and ladder-free `A1Mat` / `ApoleMat` reductions -/

end Cvs.Route.LadderFreePrimeTailCoupling
