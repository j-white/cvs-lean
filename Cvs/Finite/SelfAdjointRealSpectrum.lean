import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# A `Q`-selfadjoint matrix has real spectrum, without a quotient

Writing a would-be eigenvalue `α + iβ` as a real pair `(x, y)`, `Q`-selfadjointness forces
`β·(⟨Qx,x⟩ + ⟨Qy,y⟩) = 0`; positivity then forces `β = 0` unless both are `Q`-isotropic, and
`ker Q ⊆ ker M` collapses that case. Elementary real algebra throughout — CvS take the
separated quotient of `(ℝⁿ, Q)` and invoke the real spectral theorem there instead.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix

namespace Cvs.Finite.SelfAdjointRealSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Q : Matrix ι ι ℝ}

omit [DecidableEq ι] in
/-- **The form is symmetric.** -/
theorem dotProduct_mulVec_comm (hQ : Q.IsSymm) (x y : ι → ℝ) :
    x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : Q j i = Q i j := by rw [← Matrix.IsSymm.apply hQ]
  rw [hji]; ring

/-- **An isotropic vector of a positive semidefinite form lies in the kernel.**  The standard
`0 ≤ B(x + t y, x + t y)` argument, with an explicit `t` so no limit is taken. -/
theorem mulVec_eq_zero_of_self_eq_zero (hQ : Q.IsSymm)
    (hpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v)) {x : ι → ℝ} (hx : x ⬝ᵥ (Q *ᵥ x) = 0) :
    Q *ᵥ x = 0 := by
  have hcross : ∀ y : ι → ℝ, y ⬝ᵥ (Q *ᵥ x) = 0 := by
    intro y
    by_contra hc
    have hsym : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := dotProduct_mulVec_comm hQ x y
    have hd0 : 0 ≤ y ⬝ᵥ (Q *ᵥ y) := hpsd y
    have hden : (0:ℝ) < 1 + y ⬝ᵥ (Q *ᵥ y) := by linarith
    have hexp : ∀ t : ℝ, (x + t • y) ⬝ᵥ (Q *ᵥ (x + t • y))
        = 2 * t * (y ⬝ᵥ (Q *ᵥ x)) + t ^ 2 * (y ⬝ᵥ (Q *ᵥ y)) := by
      intro t
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hx, hsym]
      ring
    set c : ℝ := y ⬝ᵥ (Q *ᵥ x) with hcdef
    set d : ℝ := y ⬝ᵥ (Q *ᵥ y) with hddef
    have hnn := hpsd (x + (-c / (1 + d)) • y)
    rw [hexp] at hnn
    have hcsq : 0 < c ^ 2 := by positivity
    have hkey : 2 * (-c / (1 + d)) * c + (-c / (1 + d)) ^ 2 * d
        = (c ^ 2 / (1 + d)) * (-2 + d / (1 + d)) := by
      field_simp
    rw [hkey] at hnn
    have hfrac : d / (1 + d) < 1 := by rw [div_lt_one hden]; linarith
    nlinarith [hcsq, hden, hfrac, div_pos hcsq hden]
  funext i
  have h := hcross (Pi.single i 1)
  rwa [single_dotProduct, one_mul] at h

/-! ### No genuinely complex eigenvalue -/

/-- **The heart of `finmain`(i), without the quotient.**  For `Q` positive semidefinite, `M`
selfadjoint for `Q`, and `ker Q ⊆ ker M`: a real pair realising `α + iβ` with `β ≠ 0`
vanishes, so `M` has no eigenvalue off the real axis. -/
theorem eq_zero_of_complex_eigenpair {M : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v))
    (hsa : Q * M = Mᵀ * Q)
    (hker : ∀ v : ι → ℝ, Q *ᵥ v = 0 → M *ᵥ v = 0)
    {al be : ℝ} (hbe : be ≠ 0) {x y : ι → ℝ}
    (hx : M *ᵥ x = al • x - be • y) (hy : M *ᵥ y = be • x + al • y) :
    x = 0 ∧ y = 0 := by
  have hswap : ∀ v : ι → ℝ, (Q *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (Q *ᵥ v) := fun v => dotProduct_comm _ _
  have hQM : ∀ u v : ι → ℝ, (Q *ᵥ (M *ᵥ u)) ⬝ᵥ v = (Q *ᵥ u) ⬝ᵥ (M *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_mulVec, hsa, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec]
  have key := hQM x y
  rw [hx, hy] at key
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  -- `β (⟨Qx,x⟩ + ⟨Qy,y⟩) = 0`
  have hzero : be * ((Q *ᵥ x) ⬝ᵥ x + (Q *ᵥ y) ⬝ᵥ y) = 0 := by linarith [key]
  have hsum : (Q *ᵥ x) ⬝ᵥ x + (Q *ᵥ y) ⬝ᵥ y = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hbe
  rw [hswap x, hswap y] at hsum
  have hxx : x ⬝ᵥ (Q *ᵥ x) = 0 := le_antisymm (by linarith [hpsd y]) (hpsd x)
  have hyy : y ⬝ᵥ (Q *ᵥ y) = 0 := by linarith [hpsd x]
  have hMx : M *ᵥ x = 0 := hker x (mulVec_eq_zero_of_self_eq_zero hQ hpsd hxx)
  have hMy : M *ᵥ y = 0 := hker y (mulVec_eq_zero_of_self_eq_zero hQ hpsd hyy)
  rw [hMx] at hx
  rw [hMy] at hy
  have hpos : (0:ℝ) < al ^ 2 + be ^ 2 := by positivity
  have hcomp : ∀ i : ι, al * x i - be * y i = 0 ∧ be * x i + al * y i = 0 := by
    intro i
    have h1 := congrFun hx i
    have h2 := congrFun hy i
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hcomp i
    have hz : (al ^ 2 + be ^ 2) * x i = 0 := by linear_combination al * h1 + be * h2
    simpa using (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
  · obtain ⟨h1, h2⟩ := hcomp i
    have hz : (al ^ 2 + be ^ 2) * y i = 0 := by linear_combination (-be) * h1 + al * h2
    simpa using (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)

end Cvs.Finite.SelfAdjointRealSpectrum
