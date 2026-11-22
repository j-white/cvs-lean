/-
Super-algebraic Galerkin truncation convergence, reduced to the
eigenvector tail.

Super-algebraic convergence of the sections rests on one analytic
mechanism: the infinite multiplicity of the top eigenvalue admits
eigenvectors whose expansion tails in the Galerkin basis decay faster
than any algebraic rate (smooth-bump modulations). This file
formalises everything downstream of that mechanism:

* `le_norm_compress_of_top_eigenvector` — the Rayleigh bound: for any
  unit eigenvector `f` at the top eigenvalue `‖T‖` and any subspace `K`,
  `‖T‖ - ‖compress K T‖ ≤ 3 ‖T‖ · ‖f - P_K f‖`. The section error is
  controlled by the eigenvector's projection tail.
* `SuperAlgebraicDecay` — decay faster than any algebraic rate:
  `N^p · e_N → 0` for every `p`.
* `superalgebraic_sections` — the reduction: a super-algebraically
  decaying eigenvector tail forces super-algebraic convergence of the
  window-section norms.
* `tendsto_norm_section_of_eigenvector` — identification of the limit:
  a merely vanishing tail already forces the sections to converge to
  `‖T‖` itself (upgrading `tendsto_norm_section`, whose limit was only
  known to be `≤ ‖T‖`).

The tail hypothesis, a top eigenvector with super-algebraic tails, is
discharged downstream by the smooth-bump construction
(`Cvs.PathLaw.GevreyBump`, `superalgebraic_sections_atomCLMC`).
-/
import Cvs.PathLaw.Compression
import Cvs.PathLaw.RealAtom

open Filter

namespace Cvs.PathLaw

section Rayleigh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Rayleigh section bound.** For a unit eigenvector `f` at the top
eigenvalue `‖T‖`, the compression to any subspace `K` captures the norm
up to three times the projection tail of `f`. -/
theorem le_norm_compress_of_top_eigenvector
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) {f : E} (hf : ‖f‖ = 1) (hTf : T f = ‖T‖ • f) :
    ‖T‖ - 3 * ‖T‖ * ‖f - K.starProjection f‖ ≤ ‖compress K T‖ := by
  set gK : K := K.orthogonalProjectionOnto f with hgK
  have hgcoe : (gK : E) = K.starProjection f :=
    K.coe_orthogonalProjectionOnto_apply f
  set ε : ℝ := ‖f - K.starProjection f‖ with hε
  have hεnn : 0 ≤ ε := norm_nonneg _
  have hTnn : 0 ≤ ‖T‖ := norm_nonneg T
  -- the tail is orthogonal to `K`
  have hperpg : inner ℝ (f - K.starProjection f) (gK : E) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp
      (K.sub_starProjection_mem_orthogonal f) _ gK.2
  -- `‖gK‖ ≤ 1`
  have hgle : ‖(gK : E)‖ ≤ 1 := by
    rw [hgcoe]
    calc ‖K.starProjection f‖ ≤ ‖f‖ := K.norm_starProjection_apply_le f
      _ = 1 := hf
  -- `‖gK‖² ≥ 1 - 2ε`
  have hglow : (1 : ℝ) - ε ≤ ‖(gK : E)‖ := by
    have h1 := norm_sub_norm_le f (f - (gK : E))
    rw [sub_sub_cancel, hf, hgcoe, ← hε] at h1
    rw [hgcoe]
    linarith
  have hg2 : (1 : ℝ) - 2 * ε ≤ ‖(gK : E)‖ ^ 2 := by
    nlinarith [hglow, hεnn, norm_nonneg (gK : E)]
  -- the split `f = gK + tail`
  have hfsplit : f = (gK : E) + (f - K.starProjection f) := by
    rw [hgcoe]
    abel
  -- the eigenvalue equation on `gK`
  have hTg' : T (gK : E) = ‖T‖ • f - T (f - K.starProjection f) := by
    have h1 : T (gK : E) = T f - T (f - K.starProjection f) := by
      rw [← map_sub]
      congr 1
      rw [hgcoe]
      abel
    rw [h1, hTf]
  -- `⟪f, gK⟫ = ‖gK‖²`
  have hfg : inner ℝ f (gK : E) = ‖(gK : E)‖ ^ 2 := by
    conv_lhs => rw [hfsplit]
    rw [inner_add_left, real_inner_self_eq_norm_sq, hperpg, add_zero]
  -- the quadratic form identity
  have hquad : inner ℝ (T (gK : E)) (gK : E)
      = ‖T‖ * ‖(gK : E)‖ ^ 2
        - inner ℝ (T (f - K.starProjection f)) (gK : E) := by
    rw [hTg', inner_sub_left, real_inner_smul_left, hfg]
  -- the cross term is small
  have hcross : inner ℝ (T (f - K.starProjection f)) (gK : E) ≤ ‖T‖ * ε := by
    calc inner ℝ (T (f - K.starProjection f)) (gK : E)
        ≤ |inner ℝ (T (f - K.starProjection f)) (gK : E)| := le_abs_self _
      _ ≤ ‖T (f - K.starProjection f)‖ * ‖(gK : E)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ε) * 1 := by
          refine mul_le_mul ?_ hgle (norm_nonneg _)
            (mul_nonneg hTnn hεnn)
          calc ‖T (f - K.starProjection f)‖
              ≤ ‖T‖ * ‖f - K.starProjection f‖ := T.le_opNorm _
            _ = ‖T‖ * ε := by rw [← hε]
      _ = ‖T‖ * ε := mul_one _
  -- the compression dominates the quadratic form on `K`
  have hKnorm : ‖gK‖ = ‖(gK : E)‖ := rfl
  have hcompress_inner :
      inner ℝ ((compress K T) gK) gK = inner ℝ (T (gK : E)) (gK : E) := by
    have hy := (Submodule.mem_orthogonal' _ _).mp
      (K.sub_starProjection_mem_orthogonal (T (gK : E))) _ gK.2
    rw [inner_sub_left] at hy
    rw [Submodule.coe_inner, compress_apply,
      K.coe_orthogonalProjectionOnto_apply]
    linarith
  have hray : inner ℝ (T (gK : E)) (gK : E) ≤ ‖compress K T‖ := by
    rw [← hcompress_inner]
    calc inner ℝ ((compress K T) gK) gK
        ≤ |inner ℝ ((compress K T) gK) gK| := le_abs_self _
      _ ≤ ‖(compress K T) gK‖ * ‖gK‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖compress K T‖ * ‖gK‖) * ‖gK‖ :=
          mul_le_mul_of_nonneg_right ((compress K T).le_opNorm gK)
            (norm_nonneg _)
      _ ≤ ‖compress K T‖ := by
          rw [hKnorm, mul_assoc]
          calc ‖compress K T‖ * (‖(gK : E)‖ * ‖(gK : E)‖)
              ≤ ‖compress K T‖ * 1 :=
                mul_le_mul_of_nonneg_left
                  (mul_le_one₀ hgle (norm_nonneg _) hgle)
                  (norm_nonneg (compress K T))
            _ = ‖compress K T‖ := mul_one _
  -- assemble
  have hlow : ‖T‖ * (1 - 2 * ε) - ‖T‖ * ε
      ≤ inner ℝ (T (gK : E)) (gK : E) := by
    have h1 : ‖T‖ * (1 - 2 * ε) ≤ ‖T‖ * ‖(gK : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hg2 hTnn
    linarith [hquad, hcross]
  nlinarith [hray, hlow]

/-- The section error is controlled by the eigenvector tail. -/
theorem norm_sub_norm_compress_le_of_top_eigenvector
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) {f : E} (hf : ‖f‖ = 1) (hTf : T f = ‖T‖ • f) :
    ‖T‖ - ‖compress K T‖ ≤ 3 * ‖T‖ * ‖f - K.starProjection f‖ := by
  have := le_norm_compress_of_top_eigenvector K T hf hTf
  linarith

end Rayleigh

/-! ### Super-algebraic decay -/

/-- A nonnegative error sequence decays *super-algebraically* if it is
`o(N^{-p})` for every power `p`: no fixed algebraic rate describes it. -/
def SuperAlgebraicDecay (e : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, Tendsto (fun N : ℕ => (N : ℝ) ^ p * e N) atTop (nhds 0)

/-- Super-algebraic decay survives domination. -/
theorem SuperAlgebraicDecay.of_le {e e' : ℕ → ℝ} {C : ℝ}
    (h' : SuperAlgebraicDecay e') (h0 : ∀ N, 0 ≤ e N)
    (hle : ∀ N, e N ≤ C * e' N) : SuperAlgebraicDecay e := by
  intro p
  have hC := (h' p).const_mul C
  rw [mul_zero] at hC
  have hg : ∀ N : ℕ, (0 : ℝ) ≤ (N : ℝ) ^ p * e N :=
    fun N => mul_nonneg (by positivity) (h0 N)
  have hh : ∀ N : ℕ, (N : ℝ) ^ p * e N ≤ C * ((N : ℝ) ^ p * e' N) := by
    intro N
    calc (N : ℝ) ^ p * e N ≤ (N : ℝ) ^ p * (C * e' N) :=
          mul_le_mul_of_nonneg_left (hle N) (by positivity)
      _ = C * ((N : ℝ) ^ p * e' N) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC hg hh

/-- Super-algebraic decay implies plain decay (take `p = 0`). -/
theorem SuperAlgebraicDecay.tendsto_zero {e : ℕ → ℝ}
    (h : SuperAlgebraicDecay e) : Tendsto e atTop (nhds 0) := by
  have h0 := h 0
  simp only [pow_zero, one_mul] at h0
  exact h0

/-! ### The Galerkin sections of `ℓ²(ℤ)` -/

/-- **Super-algebraic Galerkin truncation convergence, reduced to the
eigenvector tail.** If the top eigenvalue of `T` on `ℓ²(ℤ)` admits a
unit eigenvector whose window-section tails decay super-algebraically,
then the section-norm errors decay super-algebraically. The tail
hypothesis is discharged by the smooth-bump construction of
`Cvs.PathLaw.GevreyBump`. -/
theorem superalgebraic_sections (T : AtomSpace →L[ℝ] AtomSpace)
    {f : AtomSpace} (hf : ‖f‖ = 1) (hTf : T f = ‖T‖ • f)
    (htail : SuperAlgebraicDecay
      fun N => ‖f - (sectionSpace N).starProjection f‖) :
    SuperAlgebraicDecay
      fun N => ‖T‖ - ‖compress (sectionSpace N) T‖ :=
  SuperAlgebraicDecay.of_le (C := 3 * ‖T‖) htail
    (fun N => sub_nonneg.mpr (norm_section_le T N))
    (fun N => norm_sub_norm_compress_le_of_top_eigenvector
      (sectionSpace N) T hf hTf)

/-- **Identification of the section limit.** A top eigenvector whose
section tails merely vanish already forces the window sections to
converge to the norm itself — upgrading `tendsto_norm_section`, whose
limit was only known to be `≤ ‖T‖`. -/
theorem tendsto_norm_section_of_eigenvector
    (T : AtomSpace →L[ℝ] AtomSpace)
    {f : AtomSpace} (hf : ‖f‖ = 1) (hTf : T f = ‖T‖ • f)
    (htail : Tendsto (fun N => ‖f - (sectionSpace N).starProjection f‖)
      atTop (nhds 0)) :
    Tendsto (fun N => ‖compress (sectionSpace N) T‖) atTop (nhds ‖T‖) := by
  have h3 := htail.const_mul (3 * ‖T‖)
  rw [mul_zero] at h3
  have hg : ∀ N : ℕ, (0 : ℝ) ≤ ‖T‖ - ‖compress (sectionSpace N) T‖ :=
    fun N => sub_nonneg.mpr (norm_section_le T N)
  have hh : ∀ N : ℕ, ‖T‖ - ‖compress (sectionSpace N) T‖
      ≤ 3 * ‖T‖ * ‖f - (sectionSpace N).starProjection f‖ :=
    fun N => norm_sub_norm_compress_le_of_top_eigenvector
      (sectionSpace N) T hf hTf
  have herr : Tendsto
      (fun N => ‖T‖ - ‖compress (sectionSpace N) T‖) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 hg hh
  have hsub := (tendsto_const_nhds (x := ‖T‖)
    (f := Filter.atTop (α := ℕ))).sub herr
  rw [sub_zero] at hsub
  simpa [sub_sub_cancel] using hsub

/-- With a vanishing-tail top eigenvector, the supremum of the section
norms is exactly the norm. -/
theorem iSup_norm_section_eq_of_eigenvector
    (T : AtomSpace →L[ℝ] AtomSpace)
    {f : AtomSpace} (hf : ‖f‖ = 1) (hTf : T f = ‖T‖ • f)
    (htail : Tendsto (fun N => ‖f - (sectionSpace N).starProjection f‖)
      atTop (nhds 0)) :
    (⨆ N, ‖compress (sectionSpace N) T‖) = ‖T‖ :=
  tendsto_nhds_unique (tendsto_norm_section T)
    (tendsto_norm_section_of_eigenvector T hf hTf htail)

/-! ### Applied to the arithmetic block -/

/-- **Super-algebraic convergence for the arithmetic block itself.** For
any real operator on `ℓ²(ℤ)` whose matrix is the Loewner atom, the
Galerkin section errors against the exact Path Law norm decay
super-algebraically, provided the top eigenvalue admits a unit
eigenvector with super-algebraically decaying section tails (supplied by
the smooth-bump construction). -/
theorem superalgebraic_sections_single_atom (q c : ℕ) (hq : 2 ≤ q)
    (hc : q < c) (T : AtomSpace →L[ℝ] AtomSpace)
    (hT : ∀ k l : ℤ,
      (T (lp.single 2 k 1) : ∀ _ : ℤ, ℝ) l = atomEntry q c k l)
    {f : AtomSpace} (hf : ‖f‖ = 1)
    (hTf : T f = pathLawNorm q c • f)
    (htail : SuperAlgebraicDecay
      fun N => ‖f - (sectionSpace N).starProjection f‖) :
    SuperAlgebraicDecay
      fun N => pathLawNorm q c - ‖compress (sectionSpace N) T‖ := by
  have hnorm := single_atom_path_lawR q c hq hc T hT
  have h := superalgebraic_sections T hf (by rw [hnorm]; exact hTf) htail
  have hfun : (fun N => pathLawNorm q c - ‖compress (sectionSpace N) T‖)
      = fun N => ‖T‖ - ‖compress (sectionSpace N) T‖ := by
    funext N
    rw [hnorm]
  rw [hfun]
  exact h

/-- **The sections of the arithmetic block converge to the Path Law norm
itself**, given a top eigenvector with merely vanishing section tails:
`λ_max(N) → pathLawNorm q c`. -/
theorem tendsto_norm_section_single_atom (q c : ℕ) (hq : 2 ≤ q)
    (hc : q < c) (T : AtomSpace →L[ℝ] AtomSpace)
    (hT : ∀ k l : ℤ,
      (T (lp.single 2 k 1) : ∀ _ : ℤ, ℝ) l = atomEntry q c k l)
    {f : AtomSpace} (hf : ‖f‖ = 1)
    (hTf : T f = pathLawNorm q c • f)
    (htail : Tendsto (fun N => ‖f - (sectionSpace N).starProjection f‖)
      atTop (nhds 0)) :
    Tendsto (fun N => ‖compress (sectionSpace N) T‖) atTop
      (nhds (pathLawNorm q c)) := by
  have hnorm := single_atom_path_lawR q c hq hc T hT
  rw [← hnorm]
  exact tendsto_norm_section_of_eigenvector T hf
    (by rw [hnorm]; exact hTf) htail

end Cvs.PathLaw
