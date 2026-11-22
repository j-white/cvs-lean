import Mathlib
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LogEnvelopeSquareSummable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Summability over the zero index

The weighted squares of the comparison function are summable over the zeros, and that function
dominates the reciprocal of one plus the ordinate, so any family the weight bounds by the square
of that reciprocal is summable.
-/

noncomputable section

namespace Cvs.Zeta.ZeroIndexSummability

open Cvs.Zeta.LogEnvelopeSquareSummable

/-- **The criterion in the comparison function**: a family the weight bounds by its square is
summable. -/
theorem summable_of_phi_sq_bound {f : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ} {C : ℝ}
    (h : ∀ rho, ‖f rho‖
      ≤ C * ((Cvs.Criterion.divisorWeight rho : ℝ) * phi |((rho : ℂ)).im| ^ 2)) :
    Summable f :=
  Summable.of_norm_bounded (summable_divisorWeight_phi_sq.mul_left C) h

/-- **The criterion in the ordinate**: a family the weight bounds by the reciprocal square of one
plus the ordinate is summable. -/
theorem summable_of_inv_sq_bound {f : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ rho, ‖f rho‖
      ≤ C * ((Cvs.Criterion.divisorWeight rho : ℝ) / (1 + |((rho : ℂ)).im|) ^ 2)) :
    Summable f := by
  refine summable_of_phi_sq_bound (C := C) fun rho => le_trans (h rho) ?_
  have habs : (0 : ℝ) ≤ |((rho : ℂ)).im| := abs_nonneg _
  have hlo : 1 / (1 + |((rho : ℂ)).im|) ≤ phi |((rho : ℂ)).im| := one_div_le_phi habs
  have hpos : (0 : ℝ) < 1 + |((rho : ℂ)).im| := by linarith
  have hw : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  have hsq : (1 / (1 + |((rho : ℂ)).im|)) ^ 2 ≤ phi |((rho : ℂ)).im| ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 / (1 + |((rho : ℂ)).im|) := by positivity
    exact pow_le_pow_left₀ h0 hlo 2
  have hrw : (Cvs.Criterion.divisorWeight rho : ℝ) / (1 + |((rho : ℂ)).im|) ^ 2
      = (Cvs.Criterion.divisorWeight rho : ℝ) * (1 / (1 + |((rho : ℂ)).im|)) ^ 2 := by
    rw [div_pow, one_pow]
    ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hw) hC

end Cvs.Zeta.ZeroIndexSummability
