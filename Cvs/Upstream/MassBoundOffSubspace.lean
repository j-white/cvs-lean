import Mathlib

/-!
# The mass bound off a subspace

A vector orthogonal to a finite orthonormal family pairs with anything only through that thing's
distance to the family's span.
-/

set_option maxHeartbeats 1600000

noncomputable section

open scoped InnerProductSpace
open Finset

namespace Cvs.Upstream.MassBoundOffSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The residual of `u` after projecting onto the family. -/
def resid (w : Fin k → E) (u : E) : E := u - ∑ i, ⟪u, w i⟫_ℝ • w i

/-- **The residual Gram.**  Projecting onto an orthonormal family removes exactly the sum of
coefficient products. -/
theorem inner_resid (w : Fin k → E) (hw : Orthonormal ℝ w) (u v : E) :
    ⟪resid w u, resid w v⟫_ℝ = ⟪u, v⟫_ℝ - ∑ i, ⟪u, w i⟫_ℝ * ⟪v, w i⟫_ℝ := by
  have hUV : ⟪u, ∑ i, ⟪v, w i⟫_ℝ • w i⟫_ℝ = ∑ i, ⟪u, w i⟫_ℝ * ⟪v, w i⟫_ℝ := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]; ring
  have hVU : ⟪∑ i, ⟪u, w i⟫_ℝ • w i, v⟫_ℝ = ∑ i, ⟪u, w i⟫_ℝ * ⟪v, w i⟫_ℝ := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => by
      rw [real_inner_smul_left, real_inner_comm (w i) v]
  have hPP : ⟪∑ i, ⟪u, w i⟫_ℝ • w i, ∑ i, ⟪v, w i⟫_ℝ • w i⟫_ℝ
      = ∑ i, ⟪u, w i⟫_ℝ * ⟪v, w i⟫_ℝ := by
    rw [hw.inner_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [resid, resid, inner_sub_left, inner_sub_right, inner_sub_right, hUV, hVU, hPP]
  ring

/-- **The residual norm is Bessel's difference.** -/
theorem norm_resid_sq (w : Fin k → E) (hw : Orthonormal ℝ w) (u : E) :
    ‖resid w u‖ ^ 2 = ‖u‖ ^ 2 - ∑ i, ⟪u, w i⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_resid w hw u u, real_inner_self_eq_norm_sq]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => (sq _).symm)

/-- **Bessel's inequality**, as the statement that the residual is a genuine remainder. -/
theorem bessel (w : Fin k → E) (hw : Orthonormal ℝ w) (u : E) :
    ∑ i, ⟪u, w i⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := norm_resid_sq w hw u
  nlinarith [sq_nonneg ‖resid w u‖, h]

end Cvs.Upstream.MassBoundOffSubspace
