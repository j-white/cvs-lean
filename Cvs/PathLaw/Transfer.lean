/-
The Single-Atom Path Law — the transfer principle, and the Path Law
assembled from two named inputs.

This file closes the *structural* gap between `Cvs.PathLaw.OpNorm` /
`Cvs.PathLaw.MaskedRotation` and the headline theorem; everything here is proved. What it shows is that the Path
Law follows from exactly two inputs, each now a precise statement about
objects that are defined in this repository rather than a prose gap:

* **(DTFT transfer)** a linear isometry equivalence `e : ℓ²(ℤ) ≃ L²(𝕋)`
  intertwining the atom `T` with the weighted masked rotation;
* **(chain norm)** `‖W‖ = chebFactor m` for the paper's
  angle and masks.

`single_atom_path_law_of` derives `‖T‖ = pathLawNorm q c` from those two.

The key reusable block proved here is `opNorm_eq_of_intertwines`: operator
norms are invariant under isometric conjugation. This is what makes the
DTFT step norm-faithful, and it is proved from
`ContinuousLinearMap.opNorm_le_bound` and `LinearIsometryEquiv.norm_map`.
-/
import Cvs.PathLaw.MaskedRotation

open MeasureTheory Real

namespace Cvs.PathLaw

/-! ### The transfer principle -/

section Transfer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Isometric conjugation preserves the operator norm.** If a linear
isometry equivalence `e` intertwines `T` with `S` (that is, `S ∘ e = e ∘ T`),
then `‖S‖ = ‖T‖`.

This is the norm-faithfulness of the DTFT step: transporting the Loewner
atom to the circle changes the space, but not the operator norm. -/
theorem opNorm_eq_of_intertwines (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) (S : F →L[𝕜] F)
    (h : ∀ x, S (e x) = e (T x)) : ‖S‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine S.opNorm_le_bound (norm_nonneg T) fun y => ?_
    have hy : e (e.symm y) = y := e.apply_symm_apply y
    calc ‖S y‖ = ‖S (e (e.symm y))‖ := by rw [hy]
      _ = ‖e (T (e.symm y))‖ := by rw [h]
      _ = ‖T (e.symm y)‖ := e.norm_map _
      _ ≤ ‖T‖ * ‖e.symm y‖ := T.le_opNorm _
      _ = ‖T‖ * ‖y‖ := by rw [e.symm.norm_map]
  · refine T.opNorm_le_bound (norm_nonneg S) fun x => ?_
    calc ‖T x‖ = ‖e (T x)‖ := (e.norm_map _).symm
      _ = ‖S (e x)‖ := by rw [h]
      _ ≤ ‖S‖ * ‖e x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [e.norm_map]

end Transfer

/-! ### The Path Law from its two inputs -/

/-- The Hilbert space `ℓ²(ℤ)` on which the Loewner atom acts. -/
abbrev AtomSpace : Type := lp (fun _ : ℤ => ℝ) 2

/-- **The Single-Atom Path Law, assembled.** Let `T` be a bounded operator
on `ℓ²(ℤ)`. Suppose

* `htransfer` — some linear isometry equivalence `e` onto `L²(AddCircle P)`
  intertwines `T` with the arithmetically weighted masked rotation
  `(Λ(q)/√q) • W` (the DTFT step); and
* `hchain` — the masked rotation has operator norm `chebFactor m`, where
  `m = ⌈log c / log q⌉` is the capacity (the chain step).

Then `‖T‖ = pathLawNorm q c = 2 cos(π/(m+1)) · Λ(q)/√q`.

Both hypotheses are statements about objects defined in this repository:
`maskedRotation` (`Cvs.PathLaw.MaskedRotation`) and `chebFactor`
(`Cvs.PathLaw.Basic`). The second is exactly the fiberwise content whose
finite-dimensional model is proved in `Cvs.PathLaw.OpNorm`
(`opNorm_pathCLM : ‖pathCLM m‖ = chebFactor m`). -/
theorem single_atom_path_law_of {P : ℝ} [Fact (0 < P)]
    (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (AddCircle P)))
    (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x))
    (hchain : ‖maskedRotation a s₁ s₂ h₁ h₂‖
        = chebFactor (capacity (Real.log c) (Real.log q))) :
    ‖T‖ = pathLawNorm q c := by
  have hnorm := opNorm_eq_of_intertwines e T
    (weight q • maskedRotation a s₁ s₂ h₁ h₂) htransfer
  rw [← hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q), hchain,
    pathLawNorm]
  ring

/-- The same conclusion in the weaker "upper bound" form: the chain estimate
`‖W‖ ≤ chebFactor m` alone already yields the Path Law bound `‖T‖ ≤ pathLawNorm q c`.
This is the half of the argument that the chain decomposition
supplies without any lower-bound (attainment) analysis. -/
theorem single_atom_path_law_le_of {P : ℝ} [Fact (0 < P)]
    (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (AddCircle P)))
    (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x))
    (hchain : ‖maskedRotation a s₁ s₂ h₁ h₂‖
        ≤ chebFactor (capacity (Real.log c) (Real.log q))) :
    ‖T‖ ≤ pathLawNorm q c := by
  have hnorm := opNorm_eq_of_intertwines e T
    (weight q • maskedRotation a s₁ s₂ h₁ h₂) htransfer
  rw [← hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q),
    pathLawNorm, mul_comm (chebFactor _) (weight q)]
  exact mul_le_mul_of_nonneg_left hchain (weight_nonneg q)

/-- **Unconditional corollary: the Weyl budget on `ℓ²(ℤ)`.** Any atom that
transfers to a weighted masked rotation obeys the universal stability cap
`‖T‖ ≤ 2Λ(q)/√q`, with *no* chain hypothesis at all — the chain
analysis is needed only to sharpen `2` to `chebFactor m`. -/
theorem opNorm_atom_le_cap_of {P : ℝ} [Fact (0 < P)]
    (q : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (AddCircle P)))
    (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x)) :
    ‖T‖ ≤ 2 * weight q := by
  have hnorm := opNorm_eq_of_intertwines e T
    (weight q • maskedRotation a s₁ s₂ h₁ h₂) htransfer
  rw [← hnorm]
  exact norm_smul_maskedRotation_le q a s₁ s₂ h₁ h₂

/-! ### Matrix coefficients determine an operator

The remaining gap (`exists_maskedRotationModel`) is a statement about matrix
coefficients. These lemmas make that precise: an operator on a Hilbert space
is determined by its matrix in any Hilbert basis, so exhibiting a basis in
which the masked rotation has the Loewner matrix is *equivalent* to
exhibiting the intertwining. -/

section Basis

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- A vector orthogonal to every basis vector is zero. -/
theorem eq_zero_of_inner_basis (b : HilbertBasis ι 𝕜 E) {v : E}
    (h : ∀ i, inner 𝕜 (b i) v = 0) : v = 0 := by
  have hrepr : b.repr v = 0 := by
    ext i
    rw [b.repr_apply_apply, h i]
    simp
  have : v = b.repr.symm (b.repr v) := (b.repr.symm_apply_apply v).symm
  rw [this, hrepr, map_zero]

omit [CompleteSpace E] in
/-- Two vectors with the same coordinates are equal. -/
theorem eq_of_inner_basis_vec (b : HilbertBasis ι 𝕜 E) {x y : E}
    (h : ∀ i, inner 𝕜 (b i) x = inner 𝕜 (b i) y) : x = y := by
  have : x - y = 0 := by
    refine eq_zero_of_inner_basis b fun i => ?_
    rw [inner_sub_right, h i, sub_self]
  exact sub_eq_zero.mp this

omit [CompleteSpace E] in
/-- Maps agreeing on a Hilbert basis are equal, even into a different space. -/
theorem eq_of_apply_basis' {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (b : HilbertBasis ι 𝕜 E) (S T : E →L[𝕜] F)
    (h : ∀ i, S (b i) = T (b i)) : S = T := by
  ext x
  have hS := (b.hasSum_repr x).mapL S
  have hT := (b.hasSum_repr x).mapL T
  have hfun : (fun i => S (b.repr x i • b i)) = fun i => T (b.repr x i • b i) := by
    funext i
    rw [map_smul, map_smul, h i]
  rw [hfun] at hS
  exact hS.unique hT

omit [CompleteSpace E] in
/-- Operators agreeing on a Hilbert basis are equal. -/
theorem eq_of_apply_basis (b : HilbertBasis ι 𝕜 E) (S T : E →L[𝕜] E)
    (h : ∀ i, S (b i) = T (b i)) : S = T := by
  ext x
  have hS := (b.hasSum_repr x).mapL S
  have hT := (b.hasSum_repr x).mapL T
  have hfun : (fun i => S (b.repr x i • b i)) = fun i => T (b.repr x i • b i) := by
    funext i
    rw [map_smul, map_smul, h i]
  rw [hfun] at hS
  exact hS.unique hT

omit [CompleteSpace E] in
/-- **Matrix coefficients determine the operator.** -/
theorem eq_of_inner_basis (b : HilbertBasis ι 𝕜 E) (S T : E →L[𝕜] E)
    (h : ∀ i j, inner 𝕜 (S (b i)) (b j) = inner 𝕜 (T (b i)) (b j)) : S = T := by
  refine eq_of_apply_basis b S T fun i => ?_
  refine eq_of_inner_basis_vec b fun j => ?_
  rw [← inner_conj_symm (𝕜 := 𝕜) (b j) (S (b i)),
    ← inner_conj_symm (𝕜 := 𝕜) (b j) (T (b i)), h i j]

end Basis

end Cvs.PathLaw
