import Mathlib

/-!
# The bottom is a line, from a form lying below

    Q ≤ Q',  every plane carries `v` with `μ₂‖v‖² ≤ Q v`,  `β < μ₂`  ⟹  no plane has `Q' ≤ β‖·‖²`

so an eigenvalue of `Q'` at or below `β` has a one-dimensional eigenspace.
`RH.md §3.23` carries what this is for.
-/

noncomputable section

namespace Cvs.WeilForm.BottomLineFromLowerForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Set.range ![x, y]` is the pair `{x, y}`. -/
theorem range_pair (x y : E) : Set.range ![x, y] = {x, y} := by
  ext z
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]

end Cvs.WeilForm.BottomLineFromLowerForm
