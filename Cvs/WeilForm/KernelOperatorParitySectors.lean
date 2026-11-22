import Mathlib

/-!
# The kernel operator on the even and odd sectors

The reflection splits the window into two closed invariant subspaces, and on each the kernel
operator is compact and symmetric, so its norm is an eigenvalue of one sign or the other.
-/

noncomputable section

namespace Cvs.WeilForm.KernelOperatorParitySectors

open MeasureTheory Set

variable {L : ℝ}

/-! ### A compact symmetric operator attains its norm -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The quadratic form of a bounded operator is bounded by its norm.** -/
theorem inner_apply_le_norm (T : E →L[ℝ] E) (x : E) :
    (inner ℝ (T x) x : ℝ) ≤ ‖T‖ * ‖x‖ ^ 2 := by
  have h1 : (inner ℝ (T x) x : ℝ) ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
  have h2 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  have h3 : ‖T x‖ * ‖x‖ ≤ (‖T‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  calc (inner ℝ (T x) x : ℝ) ≤ ‖T x‖ * ‖x‖ := h1
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := h3
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- **A nonzero compact symmetric operator has its norm as an eigenvalue of one sign.** -/
theorem hasEigenvalue_norm_or_neg (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, (inner ℝ (T x) y : ℝ) = (inner ℝ x (T y) : ℝ))
    (hcpt : IsCompactOperator T) (hne : T ≠ 0) :
    Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) ‖T‖ ∨
      Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) (-‖T‖) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hTnorm : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hne
  haveI : Nontrivial E := nontrivial_of_ne (T a) 0 (by simpa using ha)
  have hmem1 : ‖T‖ ∉ spectrum ℝ T := fun hmem =>
    h1 ((IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hTnorm).2 hmem)
  have hmem2 : -‖T‖ ∉ spectrum ℝ T := fun hmem =>
    h2 ((IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt
      (neg_ne_zero.mpr hTnorm)).2 hmem)
  have hres1 : (algebraMap ℝ ℝ) ‖T‖ ∈ resolventSet ℝ T :=
    spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp hmem1)
  have hres2 : -(algebraMap ℝ ℝ) ‖T‖ ∈ resolventSet ℝ T := by
    have : (algebraMap ℝ ℝ) (-‖T‖) ∈ resolventSet ℝ T :=
      spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp hmem2)
    simpa using this
  obtain ⟨ε, hε, hle⟩ :=
    ContinuousLinearMap.abs_rayleighQuotient_le_of_norm_mem_resolventSet T hres1 hres2
  have hsym' : (T : E →ₗ[ℝ] E).IsSymmetric := fun x y => hsym x y
  have hsup : ‖T‖ = ⨆ x, |T.rayleighQuotient x| :=
    T.norm_eq_iSup_rayleighQuotient hsym'
  have hb : (⨆ x, |T.rayleighQuotient x|) ≤ ‖T‖ - ε := ciSup_le hle
  rw [← hsup] at hb
  linarith

/-- **The norm of a nonzero compact symmetric operator is attained by an eigenvector of one
sign.** -/
theorem exists_eigenvector_norm_or_neg (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, (inner ℝ (T x) y : ℝ) = (inner ℝ x (T y) : ℝ))
    (hcpt : IsCompactOperator T) (hne : T ≠ 0) :
    (∃ x : E, x ≠ 0 ∧ T x = ‖T‖ • x) ∨ (∃ x : E, x ≠ 0 ∧ T x = (-‖T‖) • x) := by
  rcases hasEigenvalue_norm_or_neg T hsym hcpt hne with h | h
  · obtain ⟨x, hx1, hx2⟩ := h.exists_hasEigenvector
    exact Or.inl ⟨x, hx2, Module.End.mem_eigenspace_iff.mp hx1⟩
  · obtain ⟨x, hx1, hx2⟩ := h.exists_hasEigenvector
    exact Or.inr ⟨x, hx2, Module.End.mem_eigenspace_iff.mp hx1⟩

end General

/-! ### The sectors are closed -/

/-! ### The restricted operators -/

/-! ### The bottom of the truncated form on the even sector -/

/-! ### The odd sector, and the sign of the attained norm -/

/-! ### The even bottom as an exponential family -/

end Cvs.WeilForm.KernelOperatorParitySectors
