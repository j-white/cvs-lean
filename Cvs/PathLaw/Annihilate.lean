/-
The annihilating polynomial of the path graph.

`pathCharPoly m = ∏_{j} (X − 2cos θ_j)` (the Chebyshev factorization) kills
the adjacency matrix of `P_m`: since the sine eigenvectors form a complete
eigenbasis (Spectrum.lean), the product of the eigenvalue factors vanishes on
every basis vector, hence is the zero operator.

This is the finite algebraic engine of the exact spectral-set theorem for the
masked rotation: a.e. orbit chain carries `A(P_m)` or `A(P_{m-1})`, so the
product `pathCharPoly m * pathCharPoly (m-1)` annihilates the masked rotation
itself, and by polynomial spectral mapping its spectrum is contained in the
two Chebyshev families.
-/
import Cvs.PathLaw.Spectrum

open Polynomial Module

namespace Cvs.PathLaw

/-- The annihilating (characteristic) polynomial of the path graph `P_m`:
`∏_{j=0}^{m-1} (X − 2cos((j+1)π/(m+1)))`. -/
noncomputable def pathCharPoly (m : ℕ) : Polynomial ℝ :=
  ∏ j : Fin m, (X - C (2 * Real.cos (pathAngle m j)))

/-- The sine eigenvectors form a basis of `Fin m → ℝ` (for `0 < m`). -/
noncomputable def pathEigenbasis (m : ℕ) (hm : 0 < m) :
    Module.Basis (Fin m) ℝ (Fin m → ℝ) :=
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  basisOfLinearIndependentOfCardEqFinrank
    (Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (pathAdj m)) _
      (cos_pathAngle_injective m) _ (fun j => hasEigenvector_pathAdj m j))
    (Module.finrank_fintype_fun_eq_card ℝ).symm

lemma pathEigenbasis_apply (m : ℕ) (hm : 0 < m) (j : Fin m) :
    pathEigenbasis m hm j = pathEigenvector m j := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp [pathEigenbasis]

/-- Each factor of `pathCharPoly` kills its eigenvector. -/
lemma aeval_factor_pathEigenvector (m : ℕ) (j : Fin m) :
    (aeval (Matrix.toLin' (pathAdj m)) (X - C (2 * Real.cos (pathAngle m j))))
      (pathEigenvector m j) = 0 := by
  have hev := (hasEigenvector_pathAdj m j).1
  rw [Module.End.mem_eigenspace_iff] at hev
  simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, hev]
  module

/-- **Annihilation (endomorphism form).** The Chebyshev product kills the
path-graph adjacency operator. -/
theorem aeval_pathAdj_toLin' (m : ℕ) :
    aeval (Matrix.toLin' (pathAdj m)) (pathCharPoly m) = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Subsingleton.elim _ _
  · apply (pathEigenbasis m hm).ext
    intro j
    rw [pathEigenbasis_apply, LinearMap.zero_apply]
    have hfactor : pathCharPoly m
        = (∏ i ∈ Finset.univ.erase j, (X - C (2 * Real.cos (pathAngle m i))))
          * (X - C (2 * Real.cos (pathAngle m j))) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    rw [hfactor, map_mul, Module.End.mul_apply, aeval_factor_pathEigenvector,
      map_zero]

/-- **Row expansion.** Multiplying a vector by the path adjacency matrix reads
off the two neighbours, each guarded by its existence condition. This is the
discrete mirror of the masked rotation's two guarded hops. -/
theorem mulVec_pathAdj (m : ℕ) (u : Fin m → ℝ) (i : Fin m) :
    (pathAdj m).mulVec u i
      = (if h : (i : ℕ) + 1 < m then u ⟨(i : ℕ) + 1, h⟩ else 0)
        + (if _h : 1 ≤ (i : ℕ) then
            u ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
          else 0) := by
  classical
  have hsum : (pathAdj m).mulVec u i = ∑ k : Fin m, pathAdj m i k * u k := rfl
  have hentry : ∀ k : Fin m, pathAdj m i k
      = (if (i : ℕ) + 1 = (k : ℕ) then (1 : ℝ) else 0)
        + (if (k : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0) := by
    intro k
    rw [pathAdj, SimpleGraph.adjMatrix_apply]
    by_cases h1 : (i : ℕ) + 1 = (k : ℕ) <;> by_cases h2 : (k : ℕ) + 1 = (i : ℕ)
    · exfalso; omega
    · simp [SimpleGraph.pathGraph_adj, h1, h2]
    · simp [SimpleGraph.pathGraph_adj, h1, h2]
    · simp [SimpleGraph.pathGraph_adj, h1, h2]
  have hsplit : ∑ k : Fin m, pathAdj m i k * u k
      = (∑ k : Fin m, (if (i : ℕ) + 1 = (k : ℕ) then (1 : ℝ) else 0) * u k)
        + ∑ k : Fin m, (if (k : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0) * u k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry k, add_mul]
  rw [hsum, hsplit, sum_ite_coe_eq, sum_ite_succ_eq]

/-- **Annihilation (matrix form).** `pathCharPoly m` evaluated at the
adjacency matrix of `P_m` is the zero matrix. -/
theorem aeval_pathAdj (m : ℕ) :
    aeval (pathAdj m) (pathCharPoly m) = 0 := by
  apply (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin m)).injective
  rw [map_zero, ← Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv'
    (pathAdj m) (pathCharPoly m)]
  have hEq : (Matrix.toLinAlgEquiv' (pathAdj m) :
      Module.End ℝ (Fin m → ℝ)) = Matrix.toLin' (pathAdj m) := by
    ext v
    simp [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  rw [hEq]
  exact aeval_pathAdj_toLin' m

end Cvs.PathLaw
