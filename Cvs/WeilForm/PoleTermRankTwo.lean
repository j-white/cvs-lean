import Mathlib

/-!
# The pole term is exactly rank two

    poleForm = 2 · (∑ aᵢ e^{xᵢ/2}) · (∑ aⱼ e^{−xⱼ/2})

a product of two linear functionals, so it vanishes on a codimension-two subspace.  RH.md
§3.23 carries why that is the obstruction in Connes' step (a).
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset

namespace Cvs.WeilForm.PoleTermRankTwo

/-- **The pole kernel factorises exactly.**  `2cosh((u−v)/2)` is a sum of two products, each
separating `u` from `v`. -/
theorem two_cosh_split (u v : ℝ) :
    2 * Real.cosh ((u - v) / 2)
      = Real.exp (u / 2) * Real.exp (-(v / 2))
        + Real.exp (-(u / 2)) * Real.exp (v / 2) := by
  rw [Real.cosh_eq, ← Real.exp_add, ← Real.exp_add,
    show u / 2 + -(v / 2) = (u - v) / 2 by ring,
    show -(u / 2) + v / 2 = -((u - v) / 2) by ring]
  ring

/-- The pole term's quadratic form on a finite set of nodes. -/
def poleForm {ι : Type*} (s : Finset ι) (x a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * Real.cosh ((x i - x j) / 2))

/-- The two linear functionals it factors through. -/
def plusFun {ι : Type*} (s : Finset ι) (x a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, a i * Real.exp (x i / 2)

def minusFun {ι : Type*} (s : Finset ι) (x a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, a i * Real.exp (-(x i / 2))

/-- **The form is twice a product of two linear functionals.**  This is the whole of "rank
two": no eigenvector computation, just the exponential's addition law. -/
theorem poleForm_eq {ι : Type*} (s : Finset ι) (x a : ι → ℝ) :
    poleForm s x a = 2 * plusFun s x a * minusFun s x a := by
  classical
  unfold poleForm plusFun minusFun
  have hstep : ∀ i ∈ s, ∑ j ∈ s, a i * a j * (2 * Real.cosh ((x i - x j) / 2))
      = (a i * Real.exp (x i / 2)) * (∑ j ∈ s, a j * Real.exp (-(x j / 2)))
        + (a i * Real.exp (-(x i / 2))) * (∑ j ∈ s, a j * Real.exp (x j / 2)) := by
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [two_cosh_split]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **So it vanishes on a codimension-two subspace.**  Where both functionals vanish there is
no pole term at all, and what is left of the Weil form is the Toeplitz part against the
shifts. -/
theorem poleForm_eq_zero {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (h : plusFun s x a = 0) :
    poleForm s x a = 0 := by
  rw [poleForm_eq, h]
  ring

/-- Either functional vanishing is enough. -/
theorem poleForm_eq_zero' {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (h : minusFun s x a = 0) :
    poleForm s x a = 0 := by
  rw [poleForm_eq, h]
  ring

/-- **And it is a difference of squares.**  `2PM = ((P+M)² − (P−M)²)/2`, so the pole term
contributes one positive and one negative square — the negative one being what has to be
absorbed. -/
theorem poleForm_eq_sq_sub {ι : Type*} (s : Finset ι) (x a : ι → ℝ) :
    poleForm s x a
      = ((plusFun s x a + minusFun s x a) ^ 2
          - (plusFun s x a - minusFun s x a) ^ 2) / 2 := by
  rw [poleForm_eq]
  ring

end Cvs.WeilForm.PoleTermRankTwo
