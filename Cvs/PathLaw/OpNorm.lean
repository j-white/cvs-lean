/-
The Single-Atom Path Law — the operator norm of the chain model, proved.

This file upgrades the spectrum results of `Cvs.PathLaw.Spectrum` to genuine
OPERATOR-NORM statements, leaning on Mathlib's heavy machinery:

* `Matrix.toEuclideanCLM` — the star-algebra equivalence between matrices
  and continuous linear endomorphisms of `EuclideanSpace`;
* `ContinuousLinearMap.spectralRadius_eq_nnnorm` — for a self-adjoint
  operator, the spectral radius equals the norm (Rayleigh-quotient theory);
* `Matrix.spectrum_toLin'` + `Module.End.hasEigenvalue_iff_mem_spectrum` —
  transfer between matrix spectra and eigenvalues.

Results (fully proved, no `sorry`):
* `opNorm_pathCLM` — `‖P_m‖ = chebFactor m = 2 cos(π/(m+1))`: the operator
  norm of the path-graph chain operator is exactly the Chebyshev factor;
* `opNorm_smul_pathCLM` — **the Path Law on a single chain**: the chain
  operator scaled by the arithmetic weight `Λ(q)/√q` has operator norm
  exactly `pathLawNorm q c`.

The law for the masked rotation (`norm_pathLawW`, `Cvs.PathLaw.Weight`) and the
transfer from `ℓ²(ℤ)` (`Cvs.PathLaw.Model`) are proved downstream, without
direct integrals.
-/
import Cvs.PathLaw.Spectrum

open Real SimpleGraph Matrix

namespace Cvs.PathLaw

/-- The path-graph chain operator on Euclidean space. -/
noncomputable def pathCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (pathAdj m)

/-! ### Self-adjointness -/

lemma pathAdj_isHermitian (m : ℕ) : (pathAdj m).IsHermitian := by
  have h : (pathAdj m)ᵀ = pathAdj m := SimpleGraph.isSymm_adjMatrix (pathGraph m)
  show (pathAdj m)ᴴ = pathAdj m
  ext i k
  rw [Matrix.conjTranspose_apply, star_trivial]
  calc pathAdj m k i = (pathAdj m)ᵀ i k := rfl
    _ = pathAdj m i k := by rw [h]

lemma isSelfAdjoint_pathCLM (m : ℕ) : IsSelfAdjoint (pathCLM m) := by
  have h : star (pathAdj m) = pathAdj m := pathAdj_isHermitian m
  show star (pathCLM m) = pathCLM m
  unfold pathCLM
  rw [← map_star]
  exact congrArg _ h

/-! ### The spectrum of the chain operator -/

lemma spectrum_pathCLM (m : ℕ) :
    spectrum ℝ (pathCLM m)
      = Set.range fun j : Fin m => 2 * Real.cos (pathAngle m j) := by
  have h1 : spectrum ℝ (pathCLM m) = spectrum ℝ (pathAdj m) :=
    AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (𝕜 := ℝ)) (pathAdj m)
  rw [h1, ← Matrix.spectrum_toLin' (pathAdj m)]
  ext μ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := eigenvalue_eq_of_hasEigenvalue h
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    exact hasEigenvalue_pathAdj m j

/-! ### The norm -/

lemma chebFactor_nonneg (m : ℕ) (hm : 0 < m) : 0 ≤ chebFactor m := by
  unfold chebFactor
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
  have hle : π / ((m : ℝ) + 1) ≤ π / 2 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) h2
  have hnn : (0 : ℝ) ≤ π / ((m : ℝ) + 1) := by positivity
  have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos.le], hle⟩
  linarith

/-- **The operator norm of the chain.** The path-graph operator `P_m` has
`‖P_m‖ = chebFactor m = 2 cos(π/(m+1))` — the Path Law's Chebyshev factor,
now as a genuine operator norm. -/
theorem opNorm_pathCLM (m : ℕ) (hm : 0 < m) : ‖pathCLM m‖ = chebFactor m := by
  have hrad := ContinuousLinearMap.spectralRadius_eq_nnNorm (pathCLM m)
    (isSelfAdjoint_pathCLM m)
  have hsup : spectralRadius ℝ (pathCLM m) = (‖chebFactor m‖₊ : ENNReal) := by
    unfold spectralRadius
    rw [quasispectrum_eq_spectrum_union_zero, spectrum_pathCLM m]
    apply le_antisymm
    · refine iSup₂_le fun k hk => ?_
      rcases hk with ⟨j, rfl⟩ | hk0
      swap
      · rw [Set.mem_singleton_iff.mp hk0, nnNorm_zero, ENNReal.coe_zero]
        exact zero_le
      have habs : |2 * Real.cos (pathAngle m j)| ≤ chebFactor m :=
        abs_eigenvalue_le_chebFactor (hasEigenvalue_pathAdj m j)
      have hnn : ‖2 * Real.cos (pathAngle m j)‖₊ ≤ ‖chebFactor m‖₊ := by
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnNorm, Real.norm_eq_abs]
        rw [abs_of_nonneg (chebFactor_nonneg m hm)]
        exact habs
      exact_mod_cast hnn
    · have hmem : chebFactor m
          ∈ Set.range fun j : Fin m => 2 * Real.cos (pathAngle m j) := by
        refine ⟨⟨0, hm⟩, ?_⟩
        have hangle : pathAngle m ⟨0, hm⟩ = π / ((m : ℝ) + 1) := by
          unfold pathAngle
          push_cast
          ring
        show 2 * Real.cos (pathAngle m ⟨0, hm⟩) = chebFactor m
        rw [hangle]
        rfl
      exact le_biSup (fun k => (‖k‖₊ : ENNReal)) (Or.inl hmem)
  rw [hsup] at hrad
  have h2 : ‖chebFactor m‖₊ = ‖pathCLM m‖₊ := by exact_mod_cast hrad
  have h3 : ‖chebFactor m‖ = ‖pathCLM m‖ := congrArg NNReal.toReal h2
  rw [← h3, Real.norm_eq_abs, abs_of_nonneg (chebFactor_nonneg m hm)]

/-- **The Path Law on a single chain.** The chain operator of capacity
`m = ⌈log c / log q⌉`, scaled by the arithmetic weight `Λ(q)/√q`, has
operator norm exactly `pathLawNorm q c` — the Single-Atom Path Law for one
chain. -/
theorem opNorm_smul_pathCLM (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) :
    ‖weight q • pathCLM (capacity (Real.log c) (Real.log q))‖ = pathLawNorm q c := by
  have hlogq : (0 : ℝ) < Real.log q := by
    apply Real.log_pos
    have h1q : 1 < q := by omega
    exact_mod_cast h1q
  have hlogc : (0 : ℝ) < Real.log c := by
    apply Real.log_pos
    have h1c : 1 < c := by omega
    exact_mod_cast h1c
  have hcap : 0 < capacity (Real.log c) (Real.log q) := by
    unfold capacity
    rw [Nat.ceil_pos]
    exact div_pos hlogc hlogq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q),
    opNorm_pathCLM _ hcap]
  unfold pathLawNorm
  ring

end Cvs.PathLaw
