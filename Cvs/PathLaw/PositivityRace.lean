/-
The Positivity Race condition.

If the Weil quadratic form τ = F + ΔO is positive semidefinite and the
archimedean block F has a unit vector with negative Rayleigh quotient
λ, then the arithmetic block must supply at least |λ| of norm:

  ‖ΔO‖ ≥ |λ|.

This is a one-line consequence of evaluating the form at a unit vector
where the Rayleigh quotient of `F` is negative. It is a necessary condition
for positivity, not a sufficient one.
-/
import Cvs.PathLaw.MultiAtom

namespace Cvs.PathLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The positivity race condition** (Rayleigh form). If the quadratic
form of `F + D` is nonnegative, then at any unit vector the norm of `D`
dominates the negative part of the Rayleigh quotient of `F`. -/
theorem positivity_race {F D : E →L[ℝ] E}
    (hpos : ∀ u : E, 0 ≤ inner ℝ ((F + D) u) u)
    {u : E} (hu : ‖u‖ = 1) :
    -(inner ℝ (F u) u) ≤ ‖D‖ := by
  have h := hpos u
  rw [add_apply, inner_add_left] at h
  have h2 : inner ℝ (D u) u ≤ ‖D‖ := by
    calc inner ℝ (D u) u ≤ |inner ℝ (D u) u| := le_abs_self _
      _ ≤ ‖D u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖D‖ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg _)
      _ = ‖D‖ := by rw [hu]; ring
  linarith

/-- The race condition at an eigenvector: a negative eigenvalue of the
archimedean block is a lower bound for the arithmetic norm. -/
theorem positivity_race_eigenvector {F D : E →L[ℝ] E}
    (hpos : ∀ u : E, 0 ≤ inner ℝ ((F + D) u) u)
    {u : E} (hu : ‖u‖ = 1) {lam : ℝ} (hFu : F u = lam • u)
    (hlam : lam ≤ 0) :
    |lam| ≤ ‖D‖ := by
  have hinner : inner ℝ (F u) u = lam := by
    rw [hFu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    norm_num
  have h := positivity_race hpos hu (D := D)
  rw [hinner] at h
  rwa [abs_of_nonpos hlam]

end Cvs.PathLaw
