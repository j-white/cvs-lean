/-
The Single-Atom Path Law — the Chebyshev spectrum of the path graph, proved.

We lean on Mathlib throughout: the graph is `SimpleGraph.pathGraph m`
(`Mathlib.Combinatorics.SimpleGraph.Hasse`), the matrix is its `adjMatrix`,
and the eigen-machinery is `Module.End.HasEigenvector` /
`eigenvectors_linearIndependent'`.

Results (all fully proved, no `sorry`):
* `hasEigenvector_pathAdj` — `i ↦ sin((i+1)θ_j)` is an eigenvector of the
  path graph `P_m` for the eigenvalue `2 cos θ_j`, `θ_j = (j+1)π/(m+1)`;
* `hasEigenvalue_chebFactor` — in particular `chebFactor m = 2 cos(π/(m+1))`
  is an eigenvalue (the `j = 0` rung);
* `eigenvalue_eq_of_hasEigenvalue` — these `m` values are ALL the
  eigenvalues (completeness, via linear independence vs. `finrank`);
* `abs_eigenvalue_le_chebFactor` — hence every eigenvalue `μ` satisfies
  `|μ| ≤ chebFactor m`, and the bound is attained: the spectral radius of
  `P_m` is exactly the Path Law's Chebyshev factor.
-/
import Cvs.PathLaw.Basic

open Real SimpleGraph

namespace Cvs.PathLaw

/-- Path-graph adjacency is decidable, so Mathlib's `adjMatrix` applies. -/
instance (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

/-- The adjacency matrix of the path graph `P_m` over `ℝ`, from Mathlib. -/
def pathAdj (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := (pathGraph m).adjMatrix ℝ

/-- The `j`-th spectral angle `θ_j = (j+1)π/(m+1)`. -/
noncomputable def pathAngle (m : ℕ) (j : Fin m) : ℝ := ((j : ℕ) + 1) * π / (m + 1)

/-- The `j`-th eigenvector of `P_m`: `i ↦ sin((i+1)θ_j)`. -/
noncomputable def pathEigenvector (m : ℕ) (j : Fin m) : Fin m → ℝ :=
  fun i => Real.sin (((i : ℕ) + 1) * pathAngle m j)

/-! ### Angle bookkeeping -/

lemma pathAngle_pos (m : ℕ) (j : Fin m) : 0 < pathAngle m j := by
  unfold pathAngle
  have := pi_pos
  positivity

lemma pathAngle_lt_pi (m : ℕ) (j : Fin m) : pathAngle m j < π := by
  unfold pathAngle
  rw [div_lt_iff₀ (by positivity)]
  have hj : ((j : ℕ) : ℝ) + 1 < (m : ℝ) + 1 := by
    have := j.isLt
    exact_mod_cast Nat.succ_lt_succ this
  nlinarith [pi_pos]

private lemma pathAngle_le (m : ℕ) (j : Fin m) :
    pathAngle m j ≤ π - π / ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h : π - π / ((m : ℝ) + 1) = (m : ℝ) * π / ((m : ℝ) + 1) := by
    field_simp
    ring
  rw [h]
  unfold pathAngle
  gcongr
  have := j.isLt
  exact_mod_cast this

private lemma pathAngle_ge (m : ℕ) (j : Fin m) :
    π / ((m : ℝ) + 1) ≤ pathAngle m j := by
  unfold pathAngle
  rw [show π / ((m : ℝ) + 1) = 1 * π / ((m : ℝ) + 1) by ring]
  gcongr
  have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

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

/-- The chain terminates: `sin((m+1)θ_j) = sin((j+1)π) = 0`. -/
lemma sin_top (m : ℕ) (j : Fin m) :
    Real.sin (((m : ℝ) + 1) * pathAngle m j) = 0 := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h : ((m : ℝ) + 1) * pathAngle m j = (((j : ℕ) + 1 : ℕ) : ℝ) * π := by
    unfold pathAngle
    push_cast
    field_simp
  rw [h]
  exact Real.sin_nat_mul_pi ((j : ℕ) + 1)

/-! ### Indicator-sum helpers for the tridiagonal structure -/

lemma sum_ite_coe_eq {m : ℕ} (v : Fin m → ℝ) (t : ℕ) :
    (∑ k : Fin m, (if t = (k : ℕ) then (1 : ℝ) else 0) * v k)
      = if h : t < m then v ⟨t, h⟩ else 0 := by
  by_cases h : t < m
  · rw [dif_pos h, Finset.sum_eq_single (⟨t, h⟩ : Fin m)]
    · simp
    · intro k _ hk
      have hne : t ≠ (k : ℕ) := fun he => hk (Fin.ext he.symm)
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : t ≠ (k : ℕ) := fun he => h (he ▸ k.isLt)
    simp [hne]

lemma sum_ite_succ_eq {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    (∑ k : Fin m, (if (k : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0) * v k)
      = if _h : 1 ≤ (i : ℕ) then
          v ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
        else 0 := by
  by_cases h : 1 ≤ (i : ℕ)
  · rw [dif_pos h, Finset.sum_eq_single
      (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin m)]
    · simp [Nat.sub_add_cancel h]
    · intro k _ hk
      have hne : ¬((k : ℕ) + 1 = (i : ℕ)) := by
        intro he
        apply hk
        apply Fin.ext
        simp
        omega
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : ¬((k : ℕ) + 1 = (i : ℕ)) := by omega
    simp [hne]

/-! ### The eigen-equation -/

private lemma mulVec_pathEigenvector (m : ℕ) (j : Fin m) (i : Fin m) :
    (pathAdj m).mulVec (pathEigenvector m j) i
      = (2 * Real.cos (pathAngle m j)) * pathEigenvector m j i := by
  classical
  have hsum : (pathAdj m).mulVec (pathEigenvector m j) i
      = ∑ k : Fin m, pathAdj m i k * pathEigenvector m j k := rfl
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
  have hsplit : ∑ k : Fin m, pathAdj m i k * pathEigenvector m j k
      = (∑ k : Fin m, (if (i : ℕ) + 1 = (k : ℕ) then (1 : ℝ) else 0)
            * pathEigenvector m j k)
        + ∑ k : Fin m, (if (k : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0)
            * pathEigenvector m j k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry k, add_mul]
  have hS1 : (if h : (i : ℕ) + 1 < m then pathEigenvector m j ⟨(i : ℕ) + 1, h⟩ else 0)
      = Real.sin ((((i : ℕ) : ℝ) + 2) * pathAngle m j) := by
    by_cases h : (i : ℕ) + 1 < m
    · rw [dif_pos h]
      unfold pathEigenvector
      congr 1
      push_cast
      ring
    · rw [dif_neg h]
      have him : ((i : ℕ) : ℝ) + 2 = (m : ℝ) + 1 := by
        have h' : (i : ℕ) + 1 = m := by omega
        have hc := congrArg (Nat.cast : ℕ → ℝ) h'
        push_cast at hc
        linarith
      rw [him]
      exact (sin_top m j).symm
  have hS2 : (if h : 1 ≤ (i : ℕ) then
        pathEigenvector m j ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      else 0)
      = Real.sin (((i : ℕ) : ℝ) * pathAngle m j) := by
    by_cases h : 1 ≤ (i : ℕ)
    · rw [dif_pos h]
      unfold pathEigenvector
      congr 1
      rw [Nat.cast_sub h]
      push_cast
      ring
    · rw [dif_neg h]
      have h0 : (i : ℕ) = 0 := by omega
      simp [h0]
  rw [hsum, hsplit, sum_ite_coe_eq, sum_ite_succ_eq, hS1, hS2]
  have hrung := sin_rung (pathAngle m j) (i : ℕ)
  unfold pathEigenvector
  linarith [hrung]

/-! ### Eigenvectors, eigenvalues, and the resolved roadmap item -/

/-- `i ↦ sin((i+1)θ_j)` is an eigenvector of the path graph `P_m` with
eigenvalue `2 cos θ_j`. -/
theorem hasEigenvector_pathAdj (m : ℕ) (j : Fin m) :
    Module.End.HasEigenvector (Matrix.toLin' (pathAdj m))
      (2 * Real.cos (pathAngle m j)) (pathEigenvector m j) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    funext i
    have := mulVec_pathEigenvector m j i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  · intro hzero
    have h0 : pathEigenvector m j ⟨0, j.pos⟩ = 0 := by
      rw [hzero]
      rfl
    have hpos : 0 < pathEigenvector m j ⟨0, j.pos⟩ := by
      unfold pathEigenvector
      push_cast
      rw [zero_add, one_mul]
      exact Real.sin_pos_of_pos_of_lt_pi (pathAngle_pos m j) (pathAngle_lt_pi m j)
    exact absurd h0 (ne_of_gt hpos)

/-- The path graph `P_m` has eigenvalues `2 cos((j+1)π/(m+1))`. This resolves
the first roadmap item of the formalization. -/
theorem hasEigenvalue_pathAdj (m : ℕ) (j : Fin m) :
    Module.End.HasEigenvalue (Matrix.toLin' (pathAdj m))
      (2 * Real.cos (pathAngle m j)) :=
  Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_pathAdj m j)

/-- The Path Law's Chebyshev factor `2 cos(π/(m+1))` is an eigenvalue of the
path graph `P_m` (the `j = 0` rung of the staircase). -/
theorem hasEigenvalue_chebFactor (m : ℕ) (hm : 0 < m) :
    Module.End.HasEigenvalue (Matrix.toLin' (pathAdj m)) (chebFactor m) := by
  have h := hasEigenvalue_pathAdj m ⟨0, hm⟩
  have hangle : pathAngle m ⟨0, hm⟩ = π / ((m : ℝ) + 1) := by
    unfold pathAngle
    push_cast
    ring
  rw [hangle] at h
  exact h

/-! ### Completeness: these are ALL the eigenvalues -/

private lemma pathAngle_mem_Icc (m : ℕ) (j : Fin m) :
    pathAngle m j ∈ Set.Icc 0 π :=
  ⟨(pathAngle_pos m j).le, (pathAngle_lt_pi m j).le⟩

lemma cos_pathAngle_injective (m : ℕ) :
    Function.Injective fun j : Fin m => 2 * Real.cos (pathAngle m j) := by
  intro a b hab
  simp only at hab
  have hcos : Real.cos (pathAngle m a) = Real.cos (pathAngle m b) := by linarith
  have hangle := Real.injOn_cos (pathAngle_mem_Icc m a) (pathAngle_mem_Icc m b) hcos
  unfold pathAngle at hangle
  have hπ : (0 : ℝ) < π / ((m : ℝ) + 1) := by positivity
  rw [mul_div_assoc, mul_div_assoc] at hangle
  have hcast : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
    have := mul_right_cancel₀ (ne_of_gt hπ) hangle
    linarith
  exact Fin.ext (by exact_mod_cast hcast)

/-- **Completeness.** Every eigenvalue of the path graph `P_m` is one of the
`m` Chebyshev values `2 cos((j+1)π/(m+1))`: the sine eigenvectors exhaust the
spectrum. -/
theorem eigenvalue_eq_of_hasEigenvalue {m : ℕ} {μ : ℝ}
    (h : Module.End.HasEigenvalue (Matrix.toLin' (pathAdj m)) μ) :
    ∃ j : Fin m, μ = 2 * Real.cos (pathAngle m j) := by
  by_contra hc
  push Not at hc
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hinj : Function.Injective
      (fun o : Option (Fin m) => o.elim μ fun j => 2 * Real.cos (pathAngle m j)) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some jb => exact absurd hab (hc jb)
    | some ja =>
      cases b with
      | none => exact absurd hab.symm (hc ja)
      | some jb => exact congrArg some (cos_pathAngle_injective m hab)
  have heig : ∀ o : Option (Fin m),
      Module.End.HasEigenvector (Matrix.toLin' (pathAdj m))
        (o.elim μ fun j => 2 * Real.cos (pathAngle m j))
        (o.elim v (pathEigenvector m)) := by
    intro o
    cases o with
    | none => exact hv
    | some jj => exact hasEigenvector_pathAdj m jj
  have hli := Module.End.eigenvectors_linearIndependent'
    (Matrix.toLin' (pathAdj m)) _ hinj _ heig
  have hcard := hli.fintype_card_le_finrank
  simp [Fintype.card_option] at hcard

/-- **Spectral radius.** Every eigenvalue `μ` of the path graph `P_m`
satisfies `|μ| ≤ chebFactor m`, and by `hasEigenvalue_chebFactor` the bound
is attained: the spectral radius of `P_m` is exactly `2 cos(π/(m+1))`. This
is the algebraic engine of the Single-Atom Path Law. -/
theorem abs_eigenvalue_le_chebFactor {m : ℕ} {μ : ℝ}
    (h : Module.End.HasEigenvalue (Matrix.toLin' (pathAdj m)) μ) :
    |μ| ≤ chebFactor m := by
  obtain ⟨j, rfl⟩ := eigenvalue_eq_of_hasEigenvalue h
  rw [abs_le]
  constructor
  · have h1 : Real.cos (π - π / ((m : ℝ) + 1)) ≤ Real.cos (pathAngle m j) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (pathAngle_pos m j).le
        (by
          have : (0 : ℝ) ≤ π / ((m : ℝ) + 1) := by positivity
          linarith)
        (pathAngle_le m j)
    rw [Real.cos_pi_sub] at h1
    unfold chebFactor
    linarith
  · have h2 : Real.cos (pathAngle m j) ≤ Real.cos (π / ((m : ℝ) + 1)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (pathAngle_lt_pi m j).le (pathAngle_ge m j)
    unfold chebFactor
    linarith

end Cvs.PathLaw
