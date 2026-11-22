import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.LowModeRungBulkFloor
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Archimedean-Free High-Mode Tail Reduction for `RungResidualBound`

Proves that diagonal archimedean and symbol matrices preserve `lowModeRung L N C` and have
zero coupling to high modes `i ∉ lowModeSet L N C`, reducing `RungResidualBound` to the off-diagonal tail.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.HighModeTailArchFree
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.LowModeRungBulkFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Coordinate restriction and complement projection -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Coordinate restriction of a mode vector `v` to a subset `S : Set ι`.** -/
def restrictVec (S : Set ι) [DecidablePred (· ∈ S)] (v : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ S then v i else 0

omit [Fintype ι] [DecidableEq ι] in
/-- **Complement restriction of a mode vector `v` to the high-mode complement `Sᶜ`.** -/
def complVec (S : Set ι) [DecidablePred (· ∈ S)] (v : ι → ℝ) : ι → ℝ :=
  fun i => if i ∉ S then v i else 0

omit [Fintype ι] [DecidableEq ι] in
/-- `complVec S v = v - restrictVec S v`. -/
theorem complVec_eq_sub_restrictVec (S : Set ι) [DecidablePred (· ∈ S)] (v : ι → ℝ) :
    complVec S v = v - restrictVec S v := by
  ext i
  simp only [Pi.sub_apply, restrictVec, complVec]
  by_cases hi : i ∈ S <;> simp [hi]

omit [DecidableEq ι] in
/-- The squared Euclidean norm of `complVec S v` is the high-mode tail sum `∑_{i ∉ S} (v i)²`. -/
theorem complVec_dotProduct_self (S : Set ι) [DecidablePred (· ∈ S)] (v : ι → ℝ) :
    complVec S v ⬝ᵥ complVec S v = ∑ i, if i ∉ S then (v i) ^ 2 else 0 := by
  simp only [dotProduct, complVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S <;> simp [hi, sq]

omit [Fintype ι] [DecidableEq ι] in
/-- If `S` is `neg`-invariant, then `restrictVec S v` preserves `evenModeSub neg`. -/
theorem restrictVec_mem_evenModeSub (S : Set ι) [DecidablePred (· ∈ S)]
    {neg : ι → ι} (hS : ∀ i, neg i ∈ S ↔ i ∈ S)
    {v : ι → ℝ} (hv : v ∈ evenModeSub neg) :
    restrictVec S v ∈ evenModeSub neg := by
  intro i
  simp only [restrictVec]
  by_cases hi : i ∈ S
  · have hni : neg i ∈ S := (hS i).2 hi
    simp [hi, hni, hv i]
  · have hni : neg i ∉ S := fun h => hi ((hS i).1 h)
    simp [hi, hni]

/-- **If `S` is `neg`-invariant and `v ∈ evenModeSub neg`, then `restrictVec S v` lies in the
submodule spanned by `evenBasisVec neg '' S`.** -/
theorem restrictVec_mem_span_evenBasisVec (S : Set ι) [DecidablePred (· ∈ S)]
    {neg : ι → ι} (hinv : Function.Involutive neg) (hS : ∀ i, neg i ∈ S ↔ i ∈ S)
    {v : ι → ℝ} (hv : v ∈ evenModeSub neg) :
    restrictVec S v ∈ Submodule.span ℝ (evenBasisVec neg '' S) := by
  have hrev := restrictVec_mem_evenModeSub S hS hv
  rw [Cvs.Route.LowModeRungBulkFloor.eq_sum_evenBasisVec_of_even hinv hrev]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i ∈ S
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp [restrictVec, hi]

/-! ### Support containment and `negI N`-invariance of `lowModeSet` -/

omit [Fintype ι] [DecidableEq ι] in
/-- The submodule of vectors supported inside `S` (vanishing at all `i ∉ S`). -/
def suppSub (S : Set ι) : Submodule ℝ (ι → ℝ) where
  carrier := {r | ∀ i, i ∉ S → r i = 0}
  add_mem' ha hb i hi := by simp [ha i hi, hb i hi]
  zero_mem' _ _ := rfl
  smul_mem' c _ ha i hi := by simp [ha i hi]

omit [Fintype ι] in
/-- **Every vector `r ∈ Submodule.span ℝ (evenBasisVec neg '' S)` (with `S` `neg`-invariant)
vanishes at all modes `i ∉ S`.** -/
theorem apply_eq_zero_of_mem_span_evenBasisVec {S : Set ι}
    {neg : ι → ι} (hS : ∀ i, neg i ∈ S ↔ i ∈ S)
    {r : ι → ℝ} (hr : r ∈ Submodule.span ℝ (evenBasisVec neg '' S))
    {i : ι} (hi : i ∉ S) :
    r i = 0 := by
  have hle : Submodule.span ℝ (evenBasisVec neg '' S) ≤ suppSub S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩ k hk
    unfold evenBasisVec
    have hkj : k ≠ j := fun h => hk (h ▸ hj)
    have hknj : k ≠ neg j := fun h => hk (h ▸ (hS j).2 hj)
    simp [hkj, hknj]
  exact hle hr i hi

/-! ### Diagonal decoupling of `archMat` and `symbolDiagMat` from the high-mode bulk -/

/-- **The diagonal archimedean symbol matrix** `archMat L mode`:
`(archMat L mode)_{i,j} = archSymbol(2π mode(i) / L)` on the diagonal `i = j` and `0` off-diagonal. -/
def archMat (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => if i = j then Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L) else 0

/-- **The full diagonal symbol matrix** `symbolDiagMat P R L mode` (`archSymbol` minus diagonal prime cosines). -/
def symbolDiagMat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => if i = j then Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * mode i / L) else 0

/-- `(symbolDiagMat P R L mode *ᵥ r) i = symbolCut P R L (2π mode(i) / L) * r i`. -/
theorem symbolDiagMat_mulVec_apply (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (r : ι → ℝ) (i : ι) :
    (symbolDiagMat P R L mode *ᵥ r) i = Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * mode i / L) * r i := by
  simp [Matrix.mulVec, dotProduct, symbolDiagMat]

/-- **For `r ∈ Submodule.span ℝ (evenBasisVec neg '' S)` and `i ∉ S`,
`(symbolDiagMat P R L mode *ᵥ r) i = 0`.** -/
theorem symbolDiagMat_mulVec_apply_eq_zero_of_not_mem (P R : ℕ) (L : ℝ) (mode : ι → ℤ)
    {S : Set ι} {neg : ι → ι} (hS : ∀ j, neg j ∈ S ↔ j ∈ S)
    {r : ι → ℝ} (hr : r ∈ Submodule.span ℝ (evenBasisVec neg '' S))
    {i : ι} (hi : i ∉ S) :
    (symbolDiagMat P R L mode *ᵥ r) i = 0 := by
  rw [symbolDiagMat_mulVec_apply, apply_eq_zero_of_mem_span_evenBasisVec hS hr hi, mul_zero]

/-! ### Archimedean-free high-mode tail reduction of `RungResidualBound` -/

end Cvs.Route.HighModeTailArchFree
