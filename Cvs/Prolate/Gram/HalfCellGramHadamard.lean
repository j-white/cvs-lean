import Mathlib
import Cvs.Upstream.OnsetSchurCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The q-phase Hadamard decomposition of the half-cell Gram

With level-dependent wave numbers `k_a` at `s = 1/2`, the normalised half-cell Gram is exactly
`N = R̃ ∘ S^q + G`, `G_ab = −½[k]_ab sin π(q_a + q_b)/√(Q_aQ_b)`; if `[k] ⪰ 0` (true for
`k = α√(χ − β)`, a Cauchy matrix) then `|vᵀGv| ≤ ½(Σ k′_a/Q_a)‖v‖²`.
-/

noncomputable section

open Real Set MeasureTheory Matrix Finset

namespace Cvs.Prolate.Gram.HalfCellGramHadamard


/-! ### The kernel with level-dependent wave numbers -/

/-! ### The decomposition -/

section Decomp

variable {ι : Type*} [DecidableEq ι]

end Decomp

/-! ### Positivity of `[k]` for the local wave number -/

section Cauchy

variable {ι : Type*} [Fintype ι]

variable [DecidableEq ι]

end Cauchy

/-! ### The Löwner bound on `G` -/

section Bound

variable {ι : Type*} [Fintype ι]

/-- For `A ⪰ 0`, `xᵀAx ≤ tr(A)‖x‖²`. -/
theorem quad_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ A.trace * (x ⬝ᵥ x) := by
  classical
  have hent : ∀ a b, |A a b| ≤ √(A a a) * √(A b b) := by
    intro a b
    have h := Cvs.Upstream.OnsetSchurCriterion.sq_le_mul hA (Pi.single a 1) (Pi.single b 1)
    simp [Pi.single_apply, dotProduct, mulVec] at h
    rw [← Real.sqrt_mul hA.diag_nonneg, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  calc x ⬝ᵥ (A *ᵥ x) = ∑ a, ∑ b, x a * A a b * x b := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ ∑ a, ∑ b, (√(A a a) * |x a|) * (√(A b b) * |x b|) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        calc x a * A a b * x b ≤ |x a * A a b * x b| := le_abs_self _
          _ = |x a| * |A a b| * |x b| := by rw [abs_mul, abs_mul]
          _ ≤ |x a| * (√(A a a) * √(A b b)) * |x b| := by gcongr; exact hent a b
          _ = _ := by ring
    _ = (∑ a, √(A a a) * |x a|) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (∑ a, √(A a a) ^ 2) * ∑ a, |x a| ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = A.trace * (x ⬝ᵥ x) := by
        congr 1
        · simp only [Matrix.trace, Matrix.diag, Real.sq_sqrt hA.diag_nonneg]
        · simp only [dotProduct, sq, abs_mul_abs_self]

variable [DecidableEq ι]

/-! ### The floor -/

end Bound

/-! ### From the angular equation -/

end Cvs.Prolate.Gram.HalfCellGramHadamard
