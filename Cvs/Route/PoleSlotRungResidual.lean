import Mathlib
import Cvs.Route.EvenMatrixSlotPoleRestored

/-!
# Representer-Free Cross-Coupling and Rung-Residual Reduction for `ApoleSlot`

Eliminates the bulk Riesz representer `u` from `ApoleSlot` via Euclidean Cauchy–Schwarz
on the even-projected rung residual `evenProjVec (M *ᵥ r) − z` (`z ∈ Rg`).
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PoleSlotRungResidual
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Euclidean Cauchy–Schwarz, even mode projection, and orthogonal rung subtraction -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Division-free quadratic completion**: if `0 ≤ A`, `0 ≤ C`, and `B² ≤ A * C`, then `0 ≤ A + 2 * B + C`. -/
theorem quad_nonneg_of_sq_le {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : B ^ 2 ≤ A * C) :
    0 ≤ A + 2 * B + C := by
  by_cases hA0 : A = 0
  · subst hA0
    have hB0 : B = 0 := by nlinarith
    subst hB0
    linarith
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hmul : 0 ≤ A * (A + 2 * B + C) := by
      calc (0 : ℝ) ≤ (A + B) ^ 2 + (A * C - B ^ 2) := by nlinarith [sq_nonneg (A + B)]
      _ = A * (A + 2 * B + C) := by ring
    nlinarith

omit [DecidableEq ι] in
/-- `v ⬝ᵥ v` is nonnegative for any `v : ι → ℝ`. -/
theorem dotProduct_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [DecidableEq ι] in
/-- **Euclidean Cauchy–Schwarz inequality for `dotProduct` on `ι → ℝ`**:
`(u ⬝ᵥ v)² ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v)`. -/
theorem dotProduct_sq_le_mul (u v : ι → ℝ) :
    (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  simpa only [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

omit [Fintype ι] [DecidableEq ι] in
/-- **Even mode projection** `(x i + x (neg i)) / 2` under an involution `neg : ι → ι`. -/
def evenProjVec (neg : ι → ι) (x : ι → ℝ) : ι → ℝ :=
  fun i => (x i + x (neg i)) / 2

omit [Fintype ι] [DecidableEq ι] in
/-- `evenProjVec neg x` belongs to `evenModeSub neg` whenever `neg` is involutive. -/
theorem evenProjVec_mem_evenModeSub {neg : ι → ι} (hinv : Function.Involutive neg) (x : ι → ℝ) :
    evenProjVec neg x ∈ evenModeSub neg := by
  intro i
  dsimp [evenProjVec]
  rw [hinv i]
  ring

omit [DecidableEq ι] in
/-- On `evenModeSub neg`, `evenProjVec neg x` has the same dot product with `w` as `x`. -/
theorem evenProjVec_dotProduct_of_even {neg : ι → ι} (hinv : Function.Involutive neg)
    (x : ι → ℝ) {w : ι → ℝ} (hw : w ∈ evenModeSub neg) :
    evenProjVec neg x ⬝ᵥ w = x ⬝ᵥ w := by
  simp only [dotProduct, evenProjVec]
  have hsplit : (∑ i, (x i + x (neg i)) / 2 * w i)
      = (1 / 2 : ℝ) * (∑ i, x i * w i) + (1 / 2 : ℝ) * (∑ i, x (neg i) * w (neg i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw i]
    ring
  have hbij : (∑ i, x (neg i) * w (neg i)) = ∑ i, x i * w i :=
    Fintype.sum_bijective neg hinv.bijective
      (fun i => x (neg i) * w (neg i)) (fun i => x i * w i) (fun _ => rfl)
  rw [hsplit, hbij]
  ring

omit [DecidableEq ι] in
/-- Subtracting any rung vector `z ∈ R` leaves the dot product with a bulk vector `w ∈ Bulk E R` unchanged. -/
theorem dotProduct_sub_of_bulk {E R : Submodule ℝ (ι → ℝ)} (x : ι → ℝ)
    {z : ι → ℝ} (hz : z ∈ R) {w : ι → ℝ} (hw : Bulk E R w) :
    (x - z) ⬝ᵥ w = x ⬝ᵥ w := by
  rw [sub_dotProduct, hw.2 z hz, sub_zero]

omit [DecidableEq ι] in
/-- For symmetric `Q`, `r ⬝ᵥ (Q *ᵥ w) = (evenProjVec neg (Q *ᵥ r) − z) ⬝ᵥ w` for any `z ∈ R`
and `w ∈ Bulk (evenModeSub neg) R`. -/
theorem dotProduct_symm_mulVec_eq_evenProjVec_sub_of_bulk {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    {neg : ι → ι} (hinv : Function.Involutive neg)
    {R : Submodule ℝ (ι → ℝ)} (r : ι → ℝ) {z : ι → ℝ} (hz : z ∈ R)
    {w : ι → ℝ} (hw : Bulk (evenModeSub neg) R w) :
    r ⬝ᵥ (Q *ᵥ w) = (evenProjVec neg (Q *ᵥ r) - z) ⬝ᵥ w := by
  have hsym : r ⬝ᵥ (Q *ᵥ w) = (Q *ᵥ r) ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.eq]
  rw [hsym, ← evenProjVec_dotProduct_of_even hinv (Q *ᵥ r) hw.1,
    dotProduct_sub_of_bulk (evenProjVec neg (Q *ᵥ r)) hz hw]

omit [DecidableEq ι] in
/-- **Rung-residual Cauchy–Schwarz bound on the bulk**:
for symmetric `Q`, `z ∈ R`, and `w ∈ Bulk (evenModeSub neg) R`,
`(r ⬝ᵥ (Q *ᵥ w))² ≤ ((evenProjVec neg (Q *ᵥ r) − z) ⬝ᵥ (evenProjVec neg (Q *ᵥ r) − z)) * (w ⬝ᵥ w)`. -/
theorem dotProduct_symm_mulVec_sq_le_evenProjVec_sub_of_bulk {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    {neg : ι → ι} (hinv : Function.Involutive neg)
    {R : Submodule ℝ (ι → ℝ)} (r : ι → ℝ) {z : ι → ℝ} (hz : z ∈ R)
    {w : ι → ℝ} (hw : Bulk (evenModeSub neg) R w) :
    (r ⬝ᵥ (Q *ᵥ w)) ^ 2
      ≤ ((evenProjVec neg (Q *ᵥ r) - z) ⬝ᵥ (evenProjVec neg (Q *ᵥ r) - z)) * (w ⬝ᵥ w) := by
  rw [dotProduct_symm_mulVec_eq_evenProjVec_sub_of_bulk hQ hinv r hz hw]
  exact dotProduct_sq_le_mul (evenProjVec neg (Q *ᵥ r) - z) w

/-! ### Representer-free cross-coupling and rung-residual predicates -/

/-! ### Reductions from `RungResidualBound` to `ApoleFloorCrossBound`, `ApoleCrossBound`, and `ApoleSlot` -/

end Cvs.Route.PoleSlotRungResidual
