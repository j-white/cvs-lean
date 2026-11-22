/-
Compressions (finite sections) converge from below.

`compress K T = P_K ∘ T ∘ ι_K` is the compression of an operator to a
subspace with an orthogonal projection. Two facts drive the paper's
finite-truncation statement (Section 4, qualitative part):

* `norm_compress_le` — a compression never exceeds the norm;
* `norm_compress_mono` — compressions to nested subspaces have monotone
  norms (the finite sections increase).

Instantiated to the window subspaces `span {e_k : |k| ≤ N}` of `ℓ²(ℤ)`, the
section norms of any operator form a monotone sequence bounded by `‖T‖`,
hence converge (from below) to their supremum `≤ ‖T‖`
(`tendsto_norm_section`). The *rate* of convergence, and the identification
of the limit with `‖T‖`, remain outside the formalisation.
-/
import Cvs.PathLaw.Transfer
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open Submodule

namespace Cvs.PathLaw

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- The compression (finite section) of `T` to the subspace `K`:
`P_K ∘ T ∘ ι_K`. -/
noncomputable def compress (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : K →L[𝕜] K :=
  K.orthogonalProjectionOnto ∘L (T ∘L K.subtypeL)

lemma norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact le_of_eq rfl

/-- Projection–inclusion composites are contractions. -/
lemma norm_proj_comp_subtypeL_le (K L : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    ‖K.orthogonalProjectionOnto ∘L L.subtypeL‖ ≤ 1 := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  calc ‖K.orthogonalProjectionOnto‖ * ‖L.subtypeL‖
      ≤ 1 * 1 :=
        mul_le_mul (orthogonalProjectionOnto_norm_le K) (norm_subtypeL_le L)
          (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Compression never exceeds the norm.** -/
theorem norm_compress_le (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : ‖compress K T‖ ≤ ‖T‖ := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul (orthogonalProjectionOnto_norm_le K)
    (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one) ?_
  rw [one_mul]
  calc ‖T‖ * ‖K.subtypeL‖ ≤ ‖T‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_subtypeL_le K) (norm_nonneg _)
    _ = ‖T‖ := mul_one _

/-- Projections compose along nested subspaces: `P₁ ∘ S₂ = P₁`. -/
lemma orthogonalProjectionOnto_starProjection {K₁ K₂ : Submodule 𝕜 E}
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection] (h : K₁ ≤ K₂)
    (y : E) :
    K₁.orthogonalProjectionOnto (K₂.starProjection y)
      = K₁.orthogonalProjectionOnto y := by
  have hmem : K₂.starProjection y - y ∈ K₁ᗮ := by
    have h1 := K₂.sub_starProjection_mem_orthogonal y
    have h2 := Submodule.orthogonal_le h h1
    simpa [neg_sub] using neg_mem h2
  have h0 : K₁.orthogonalProjectionOnto (K₂.starProjection y - y) = 0 :=
    orthogonalProjectionOnto_apply_of_mem_orthogonal hmem
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- **Compression norms are monotone in the subspace.** -/
theorem norm_compress_mono {K₁ K₂ : Submodule 𝕜 E}
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h : K₁ ≤ K₂) (T : E →L[𝕜] E) :
    ‖compress K₁ T‖ ≤ ‖compress K₂ T‖ := by
  have hfact : compress K₁ T
      = (K₁.orthogonalProjectionOnto ∘L K₂.subtypeL) ∘L
          (compress K₂ T ∘L
            (K₂.orthogonalProjectionOnto ∘L K₁.subtypeL)) := by
    ext x
    have hx2 : (x : E) ∈ K₂ := h x.2
    have hBx : K₂.orthogonalProjectionOnto (x : E) = ⟨(x : E), hx2⟩ :=
      orthogonalProjectionOnto_mem_subspace_eq_self (⟨(x : E), hx2⟩ : K₂)
    have hBxc : ((K₂.orthogonalProjectionOnto (x : E) : K₂) : E) = (x : E) :=
      congrArg Subtype.val hBx
    show ((K₁.orthogonalProjectionOnto (T (x : E)) : K₁) : E)
        = ((K₁.orthogonalProjectionOnto
            ((K₂.orthogonalProjectionOnto
              (T ((K₂.orthogonalProjectionOnto (x : E) : K₂) : E)) : K₂) : E)
            : K₁) : E)
    rw [hBxc]
    exact (congrArg Subtype.val
      (orthogonalProjectionOnto_starProjection h (T (x : E)))).symm
  rw [hfact]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul (norm_proj_comp_subtypeL_le K₁ K₂)
    (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one) ?_
  rw [one_mul]
  calc ‖compress K₂ T‖ * ‖K₂.orthogonalProjectionOnto ∘L K₁.subtypeL‖
      ≤ ‖compress K₂ T‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_proj_comp_subtypeL_le K₂ K₁)
          (norm_nonneg _)
    _ = ‖compress K₂ T‖ := mul_one _

/-! ### Compression algebra on invariant subspaces -/

lemma compress_apply (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (T : E →L[𝕜] E) (x : K) :
    compress K T x = K.orthogonalProjectionOnto (T x) := rfl

lemma compress_add (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (T S : E →L[𝕜] E) :
    compress K (T + S) = compress K T + compress K S := by
  ext x
  show ((K.orthogonalProjectionOnto ((T + S) (x : E)) : K) : E) = _
  rw [add_apply, map_add]
  rfl

lemma compress_smul (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (a : 𝕜) (T : E →L[𝕜] E) :
    compress K (a • T) = a • compress K T := by
  ext x
  show ((K.orthogonalProjectionOnto ((a • T) (x : E)) : K) : E) = _
  rw [smul_apply, map_smul]
  rfl

lemma compress_one (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    compress K (1 : E →L[𝕜] E) = 1 := by
  ext x
  show ((K.orthogonalProjectionOnto ((1 : E →L[𝕜] E) (x : E)) : K) : E) = _
  rw [one_apply_eq_self]
  exact congrArg Subtype.val
    (orthogonalProjectionOnto_mem_subspace_eq_self x)

/-- On an invariant subspace, compression is multiplicative. -/
lemma compress_mul_of_invariant {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {T S : E →L[𝕜] E}
    (hS : ∀ x ∈ K, S x ∈ K) :
    compress K (T * S) = compress K T * compress K S := by
  ext x
  have hSx : ((K.orthogonalProjectionOnto (S (x : E)) : K) : E) = S (x : E) :=
    congrArg Subtype.val (orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨S (x : E), hS _ x.2⟩ : K))
  show ((K.orthogonalProjectionOnto (T (S (x : E))) : K) : E)
      = ((K.orthogonalProjectionOnto
          (T ((K.orthogonalProjectionOnto (S (x : E)) : K) : E)) : K) : E)
  rw [hSx]

/-- On an invariant subspace, compression commutes with powers. -/
lemma compress_pow_of_invariant {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {T : E →L[𝕜] E}
    (hT : ∀ x ∈ K, T x ∈ K) (n : ℕ) :
    compress K (T ^ n) = (compress K T) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, compress_one]
  | succ n IH =>
    rw [pow_succ, pow_succ, compress_mul_of_invariant hT, IH]

lemma compress_zero (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    compress K (0 : E →L[𝕜] E) = 0 := by
  ext x
  show ((K.orthogonalProjectionOnto ((0 : E →L[𝕜] E) (x : E)) : K) : E) = _
  rw [zero_apply, map_zero]
  rfl

lemma compress_sum (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {ι : Type*} (s : Finset ι) (F : ι → (E →L[𝕜] E)) :
    compress K (∑ i ∈ s, F i) = ∑ i ∈ s, compress K (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [compress_zero]
  | insert i s hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, compress_add, IH]

/-- On an invariant subspace, compression commutes with polynomial
functional calculus. -/
lemma aeval_compress_of_invariant {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {T : E →L[𝕜] E}
    (hT : ∀ x ∈ K, T x ∈ K) (q : Polynomial 𝕜) :
    Polynomial.aeval (compress K T) q
      = compress K (Polynomial.aeval T q) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    compress_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [compress_smul, compress_pow_of_invariant hT]

end Abstract

/-! ### Finite sections of operators on `ℓ²(ℤ)` -/

/-- The window subspace of `ℓ²(ℤ)` spanned by the standard basis vectors
with `|k| ≤ N`. -/
noncomputable def sectionSpace (N : ℕ) : Submodule ℝ AtomSpace :=
  span ℝ ((fun k : ℤ => lp.single 2 k (1 : ℝ)) '' {k : ℤ | |k| ≤ (N : ℤ)})

instance sectionSpace_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (sectionSpace N) := by
  apply FiniteDimensional.span_of_finite
  apply Set.Finite.image
  have hsub : {k : ℤ | |k| ≤ (N : ℤ)} ⊆ Set.Icc (-(N : ℤ)) N := fun k hk =>
    Set.mem_Icc.mpr (abs_le.mp hk)
  exact (Set.finite_Icc _ _).subset hsub

theorem sectionSpace_mono {M N : ℕ} (h : M ≤ N) :
    sectionSpace M ≤ sectionSpace N := by
  apply span_mono
  apply Set.image_mono
  intro k hk
  have hk' : |k| ≤ (M : ℤ) := hk
  have hMN : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  exact le_trans hk' hMN

/-- The window-section norms are monotone. -/
theorem norm_section_mono (T : AtomSpace →L[ℝ] AtomSpace) :
    Monotone fun N => ‖compress (sectionSpace N) T‖ := fun _ _ h =>
  norm_compress_mono (sectionSpace_mono h) T

/-- The window-section norms are capped by the operator norm. -/
theorem norm_section_le (T : AtomSpace →L[ℝ] AtomSpace) (N : ℕ) :
    ‖compress (sectionSpace N) T‖ ≤ ‖T‖ :=
  norm_compress_le _ T

/-- **Finite sections converge from below**: the window-section norms of any
operator on `ℓ²(ℤ)` increase to their supremum, which is at most `‖T‖`. -/
theorem tendsto_norm_section (T : AtomSpace →L[ℝ] AtomSpace) :
    Filter.Tendsto (fun N => ‖compress (sectionSpace N) T‖) Filter.atTop
      (nhds (⨆ N, ‖compress (sectionSpace N) T‖)) :=
  tendsto_atTop_ciSup (norm_section_mono T)
    ⟨‖T‖, by rintro x ⟨N, rfl⟩; exact norm_section_le T N⟩

theorem iSup_norm_section_le (T : AtomSpace →L[ℝ] AtomSpace) :
    (⨆ N, ‖compress (sectionSpace N) T‖) ≤ ‖T‖ :=
  ciSup_le (norm_section_le T)

end Cvs.PathLaw
