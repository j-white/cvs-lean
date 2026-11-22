import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/
/-
# B0.  The path-graph spectrum

`‖P_m‖ = 2 cos(π/(m+1))`, the one input to the norm law that Mathlib does not
provide.  Mathlib knows a Hermitian matrix has eigenvalues and relates them to
its spectrum; it does not know the eigenvalues of `SimpleGraph.pathGraph`.
Those are constructed here: `i ↦ sin((i+1)θ_j)` with `θ_j = (j+1)π/(m+1)`.
-/

open Real SimpleGraph Matrix

namespace Cvs.Operator

/-! ### Angle bookkeeping -/

/-! ### The three-term sine recurrence (the divided-difference rung) -/

/-- The three-term sine recurrence underlying the path-graph eigenvectors:
`sin(kθ) + sin((k+2)θ) = 2cos θ · sin((k+1)θ)`. Reused on the circle as the
Schur condition for the chain weight. -/
theorem sin_rung (θ : ℝ) (k : ℕ) :
    Real.sin ((k : ℝ) * θ) + Real.sin (((k : ℝ) + 2) * θ)
      = 2 * Real.cos θ * Real.sin (((k : ℝ) + 1) * θ) := by
  have h1 : ((k : ℝ) + 2) * θ = ((k : ℝ) + 1) * θ + θ := by ring
  have h2 : (k : ℝ) * θ = ((k : ℝ) + 1) * θ - θ := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-! ### Indicator-sum helpers for the tridiagonal structure -/

/-! ### The eigen-equation -/

/-! ### Eigenvectors, eigenvalues, and the resolved roadmap item -/

/-! ### Completeness: these are ALL the eigenvalues -/

/-! ### Self-adjointness -/

/-! ### The spectrum of the chain operator -/

/-! ### The norm -/

lemma chebFactor_nonneg (m : ℕ) (hm : 0 < m) : 0 ≤ Cvs.Operator.chebFactor m := by
  unfold Cvs.Operator.chebFactor
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
  have hle : π / ((m : ℝ) + 1) ≤ π / 2 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) h2
  have hnn : (0 : ℝ) ≤ π / ((m : ℝ) + 1) := by positivity
  have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos.le], hle⟩
  linarith

end Cvs.Operator
