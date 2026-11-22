import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Cvs.Finite.DividedDifferenceCommutator

/-!
# The shifted diagonal, and where simplicity enters

Subtracting `lam` from the diagonal keeps the divided-difference form, leaving `b` and `pos`
untouched, and the shifted kernel is a line exactly when `lam` is a simple eigenvalue of the
unshifted matrix.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix Cvs.Finite.DividedDifferenceCommutator

namespace Cvs.Finite.ShiftedDiagonalSimplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal, shifted by `lam`. -/
def shiftDiag (a : ι → ℝ) (lam : ℝ) : ι → ℝ := fun i => a i - lam

/-- **The shift only moves the diagonal**, which is `ddMatrix`'s free parameter. -/
theorem ddMatrix_sub_smul (a b pos : ι → ℝ) (lam : ℝ) :
    ddMatrix a b pos - lam • (1 : Matrix ι ι ℝ) = ddMatrix (shiftDiag a lam) b pos := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ddMatrix, shiftDiag, Matrix.one_apply]
  · simp [ddMatrix, shiftDiag, Matrix.one_apply, h]

/-- **The shift acts on a vector by subtracting `lam • v`.** -/
theorem mulVec_shift (a b pos : ι → ℝ) (lam : ℝ) (v : ι → ℝ) :
    ddMatrix (shiftDiag a lam) b pos *ᵥ v = ddMatrix a b pos *ᵥ v - lam • v := by
  rw [← ddMatrix_sub_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Where Gap 1 enters.**  The shifted kernel is the line through `xi` exactly when the
`lam`-eigenspace of the unshifted matrix is. -/
theorem kerline_shift_iff (a b pos : ι → ℝ) (lam : ℝ) (xi : ι → ℝ) :
    (∀ v : ι → ℝ, ddMatrix (shiftDiag a lam) b pos *ᵥ v = 0 → ∃ c : ℝ, v = c • xi)
      ↔ (∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi) := by
  constructor
  · intro h v hv
    exact h v (by rw [mulVec_shift, hv, sub_self])
  · intro h v hv
    refine h v ?_
    have hs := mulVec_shift a b pos lam v
    rw [hv] at hs
    exact sub_eq_zero.mp hs.symm

end Cvs.Finite.ShiftedDiagonalSimplicity
