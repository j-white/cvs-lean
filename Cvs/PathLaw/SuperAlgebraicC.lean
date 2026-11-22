/-
The complex Rayleigh reduction and the unconditional assembly
(rapid-decay campaign, stage 7).

The Rayleigh section bound generalizes to complex Hilbert space by
taking real parts, and everything assembles: the bump eigenfunction
transports through `ofRealLp` and the DTFT to an eigenvector of the
canonical atom `atomCLMC` at its top eigenvalue `pathLawNorm q c`, with
super-algebraically decaying `sectionSpaceC` tails. Consequently

  `pathLawNorm q c − ‖P_N T P_N‖`,   `T = atomCLMC q c`, `P_N` onto `span {e_k : |k| ≤ N}`,

decays super-algebraically — the rate for the unfolded sections stated in
Section 4 of the paper — for any atom that admits a smooth bump whose
support survives on the long-chain base (a nonvanishing-slice
hypothesis discharged by an explicit bump construction).
-/
import Cvs.PathLaw.TailTransport

open MeasureTheory Real Submodule
open scoped ContDiff

namespace Cvs.PathLaw

local notation "𝕋₁" => AddCircle (1 : ℝ)
local notation "L2V" => Lp ℂ 2 (volume : Measure 𝕋₁)

section RayleighC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The complex Rayleigh section bound**: the real-part Rayleigh
quotient argument, verbatim. -/
theorem le_norm_compress_of_top_eigenvector_C
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →L[ℂ] E) {f : E} (hf : ‖f‖ = 1)
    (hTf : T f = ((‖T‖ : ℝ) : ℂ) • f) :
    ‖T‖ - 3 * ‖T‖ * ‖f - K.starProjection f‖ ≤ ‖compress K T‖ := by
  set gK : K := K.orthogonalProjectionOnto f with hgK
  have hgcoe : (gK : E) = K.starProjection f :=
    K.coe_orthogonalProjectionOnto_apply f
  set ε : ℝ := ‖f - K.starProjection f‖ with hε
  have hεnn : 0 ≤ ε := norm_nonneg _
  have hTnn : 0 ≤ ‖T‖ := norm_nonneg T
  have hperpg : inner ℂ (f - K.starProjection f) (gK : E) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp
      (K.sub_starProjection_mem_orthogonal f) _ gK.2
  have hgle : ‖(gK : E)‖ ≤ 1 := by
    rw [hgcoe]
    calc ‖K.starProjection f‖ ≤ ‖f‖ := K.norm_starProjection_apply_le f
      _ = 1 := hf
  have hglow : (1 : ℝ) - ε ≤ ‖(gK : E)‖ := by
    have h1 := norm_sub_norm_le f (f - (gK : E))
    rw [sub_sub_cancel, hf, hgcoe, ← hε] at h1
    rw [hgcoe]
    linarith
  have hg2 : (1 : ℝ) - 2 * ε ≤ ‖(gK : E)‖ ^ 2 := by
    nlinarith [hglow, hεnn, norm_nonneg (gK : E)]
  have hfsplit : f = (gK : E) + (f - K.starProjection f) := by
    rw [hgcoe]
    abel
  have hTg' : T (gK : E)
      = ((‖T‖ : ℝ) : ℂ) • f - T (f - K.starProjection f) := by
    have h1 : T (gK : E) = T f - T (f - K.starProjection f) := by
      rw [← map_sub]
      congr 1
      rw [hgcoe]
      abel
    rw [h1, hTf]
  have hfg : inner ℂ f (gK : E) = ((‖(gK : E)‖ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hfsplit]
    rw [inner_add_left, hperpg, add_zero, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hquad : (inner ℂ (T (gK : E)) (gK : E)).re
      = ‖T‖ * ‖(gK : E)‖ ^ 2
        - (inner ℂ (T (f - K.starProjection f)) (gK : E)).re := by
    rw [hTg', inner_sub_left, inner_smul_left, Complex.conj_ofReal, hfg]
    have hmul : ((‖T‖ : ℝ) : ℂ) * ((‖(gK : E)‖ ^ 2 : ℝ) : ℂ)
        = ((‖T‖ * ‖(gK : E)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hmul, Complex.sub_re, Complex.ofReal_re]
  have hcross : (inner ℂ (T (f - K.starProjection f)) (gK : E)).re
      ≤ ‖T‖ * ε := by
    calc (inner ℂ (T (f - K.starProjection f)) (gK : E)).re
        ≤ ‖inner ℂ (T (f - K.starProjection f)) (gK : E)‖ :=
          Complex.re_le_norm _
      _ ≤ ‖T (f - K.starProjection f)‖ * ‖(gK : E)‖ :=
          norm_inner_le_norm _ _
      _ ≤ (‖T‖ * ε) * 1 := by
          refine mul_le_mul ?_ hgle (norm_nonneg _)
            (mul_nonneg hTnn hεnn)
          calc ‖T (f - K.starProjection f)‖
              ≤ ‖T‖ * ‖f - K.starProjection f‖ := T.le_opNorm _
            _ = ‖T‖ * ε := by rw [← hε]
      _ = ‖T‖ * ε := mul_one _
  have hKnorm : ‖gK‖ = ‖(gK : E)‖ := rfl
  have hcompress_inner :
      inner ℂ ((compress K T) gK) gK = inner ℂ (T (gK : E)) (gK : E) := by
    have hy := (Submodule.mem_orthogonal' _ _).mp
      (K.sub_starProjection_mem_orthogonal (T (gK : E))) _ gK.2
    rw [inner_sub_left] at hy
    rw [Submodule.coe_inner, compress_apply,
      K.coe_orthogonalProjectionOnto_apply]
    exact (sub_eq_zero.mp hy).symm
  have hray : (inner ℂ (T (gK : E)) (gK : E)).re ≤ ‖compress K T‖ := by
    rw [← hcompress_inner]
    calc (inner ℂ ((compress K T) gK) gK).re
        ≤ ‖inner ℂ ((compress K T) gK) gK‖ := Complex.re_le_norm _
      _ ≤ ‖(compress K T) gK‖ * ‖gK‖ := norm_inner_le_norm _ _
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
  have hlow : ‖T‖ * (1 - 2 * ε) - ‖T‖ * ε
      ≤ (inner ℂ (T (gK : E)) (gK : E)).re := by
    have h1 : ‖T‖ * (1 - 2 * ε) ≤ ‖T‖ * ‖(gK : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hg2 hTnn
    linarith [hquad, hcross]
  nlinarith [hray, hlow]

/-- The complex section-error bound. -/
theorem norm_sub_norm_compress_le_of_top_eigenvector_C
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →L[ℂ] E) {f : E} (hf : ‖f‖ = 1)
    (hTf : T f = ((‖T‖ : ℝ) : ℂ) • f) :
    ‖T‖ - ‖compress K T‖ ≤ 3 * ‖T‖ * ‖f - K.starProjection f‖ := by
  have := le_norm_compress_of_top_eigenvector_C K T hf hTf
  linarith

/-- **The complex super-algebraic reduction**, for any family of
subspaces with orthogonal projections. -/
theorem superalgebraic_compress_C (K : ℕ → Submodule ℂ E)
    [∀ N, (K N).HasOrthogonalProjection]
    (T : E →L[ℂ] E) {f : E} (hf : ‖f‖ = 1)
    (hTf : T f = ((‖T‖ : ℝ) : ℂ) • f)
    (htail : SuperAlgebraicDecay
      fun N => ‖f - (K N).starProjection f‖) :
    SuperAlgebraicDecay fun N => ‖T‖ - ‖compress (K N) T‖ :=
  SuperAlgebraicDecay.of_le (C := 3 * ‖T‖) htail
    (fun N => sub_nonneg.mpr (norm_compress_le (K N) T))
    (fun N => norm_sub_norm_compress_le_of_top_eigenvector_C (K N) T hf hTf)

end RayleighC

/-! ### Eigen-equation transport -/

/-- The volume-`L²` bump eigenfunction is the complexification of the
real one. -/
theorem rungFunCV_eq_ofRealLp (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    rungFunCV β hβ L j c hcm B hB hbd
      = ofRealLp (rungFunL2 β hβ L j c hcm B hB hbd) := by
  have hcv : (rungFunCV β hβ L j c hcm B hB hbd : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[volume] fun z => ((rungFun β L j c z : ℝ) : ℂ) :=
    MemLp.coeFn_toLp _
  have hrl : ((rungFunL2 β hβ L j c hcm B hB hbd :
      AddCircle (1 : ℝ) → ℝ)) =ᵐ[volume] rungFun β L j c :=
    MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [hcv,
    coeFn_ofRealLp (rungFunL2 β hβ L j c hcm B hB hbd), hrl]
    with z h1 h2 h3
  rw [h1, h2, h3]

/-- The eigen-equation for the complexified bump eigenfunction. -/
theorem pathLawWC_rungFunCV (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    pathLawWC β (rungFunCV β hβ L j c hcm B hB hbd)
      = ((2 * Real.cos (pathAngle L j) : ℝ) : ℂ)
          • rungFunCV β hβ L j c hcm B hB hbd := by
  rw [rungFunCV_eq_ofRealLp]
  have h1 : pathLawWC β (ofRealLp (rungFunL2 β hβ L j c hcm B hB hbd))
      = ofRealLp (pathLawW β (rungFunL2 β hβ L j c hcm B hB hbd)) :=
    (ofRealLp_maskedRotation _ _ _ _ _ _).symm
  rw [h1, pathLawW_rungFunL2, ofRealLp_smul]

/-- The top rung angle gives the Chebyshev factor. -/
lemma two_cos_pathAngle_zero' (m : ℕ) (hm : 0 < m) :
    2 * Real.cos (pathAngle m ⟨0, hm⟩) = chebFactor m := by
  rw [pathAngle, chebFactor]
  norm_num

/-- **Unconditional super-algebraic Galerkin convergence for the
canonical atom**, given a smooth bump surviving on the long-chain base:
`pathLawNorm q c − ‖P_N T P_N‖` (unfolded sections of `T = atomCLMC q c`)
decays faster than any algebraic rate. -/
theorem superalgebraic_sections_atomCLMC_of_bump (q c : ℕ) (hq : 2 ≤ q)
    (hc : q < c) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsupp : tsupport b ⊆ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 (Real.log q / Real.log c) : ℝ) - 1)
        * (Real.log q / Real.log c)))
    (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < Real.log q / Real.log c → |b r| ≤ B)
    (hvol : 0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet (Real.log q / Real.log c)
            (capacity 1 (Real.log q / Real.log c))
        ∧ chainPos (Real.log q / Real.log c) (rep z) = 0
        ∧ b (chainBase (Real.log q / Real.log c) (rep z)) ≠ 0}) :
    SuperAlgebraicDecay fun N =>
      pathLawNorm q c - ‖compress (sectionSpaceC N) (atomCLMC q c)‖ := by
  obtain ⟨hβ, hβ1⟩ := beta_mem q c hq hc
  have hm0 : 0 < capacity 1 (Real.log q / Real.log c) :=
    one_le_capacity _ hβ
  set F : L2V := rungFunCV (Real.log q / Real.log c) hβ
    (capacity 1 (Real.log q / Real.log c)) ⟨0, hm0⟩ b hbm B hB hbd with hFdef
  set g : AtomSpaceC := dtft.symm F with hgdef
  -- nonvanishing
  have hFne : F ≠ 0 := by
    rw [hFdef, rungFunCV_eq_ofRealLp]
    exact ofRealLp_ne_zero
      (rungFunL2_ne_zero _ hβ _ _ b hbm B hB hbd hvol)
  have hg0 : g ≠ 0 := by
    intro h0
    apply hFne
    have := congrArg dtft h0
    rwa [hgdef, dtft.apply_symm_apply, map_zero] at this
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg0
  -- the eigen-equation for `g`
  have hcap : capacity 1 (Real.log q / Real.log c)
      = capacity (Real.log c) (Real.log q) := capacity_one_div _ _
  have hlam : weight q
        * (2 * Real.cos (pathAngle (capacity 1 (Real.log q / Real.log c))
            ⟨0, hm0⟩))
      = pathLawNorm q c := by
    rw [two_cos_pathAngle_zero' _ hm0, pathLawNorm, hcap, mul_comm]
  have heig : atomCLMC q c g = ((pathLawNorm q c : ℝ) : ℂ) • g := by
    have h1 : atomCLMC q c g
        = dtft.symm ((((weight q : ℝ) : ℂ)
            • pathLawWC (Real.log q / Real.log c)) (dtft g)) := rfl
    rw [h1, hgdef, dtft.apply_symm_apply]
    rw [smul_apply, pathLawWC_rungFunCV]
    rw [smul_smul, map_smul]
    congr 1
    rw [← hlam]
    push_cast
    ring
  -- the normalized eigenvector
  set u : AtomSpaceC := ((‖g‖⁻¹ : ℝ) : ℂ) • g with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact inv_mul_cancel₀ hgn
  have hTnorm : ‖atomCLMC q c‖ = pathLawNorm q c :=
    opNorm_atomCLMC q c hq hc
  have hTu : atomCLMC q c u
      = ((‖atomCLMC q c‖ : ℝ) : ℂ) • u := by
    rw [hudef, map_smul, heig, hTnorm, smul_comm]
  -- tails of the normalized eigenvector
  have htailg := superAlgebraic_sectionSpaceC_tail
    (Real.log q / Real.log c) hβ ⟨0, hm0⟩ b hb hsupp hbm B hB hbd
  have htailu : SuperAlgebraicDecay
      fun N => ‖u - (sectionSpaceC N).starProjection u‖ := by
    refine SuperAlgebraicDecay.of_le (C := ‖g‖⁻¹) htailg
      (fun N => norm_nonneg _) (fun N => ?_)
    have hPu : (sectionSpaceC N).starProjection u
        = ((‖g‖⁻¹ : ℝ) : ℂ) • (sectionSpaceC N).starProjection g := by
      rw [hudef, map_smul]
    rw [hudef, hPu, ← smul_sub, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- assemble
  have h := superalgebraic_compress_C (fun N => sectionSpaceC N)
    (atomCLMC q c) hu1 hTu htailu
  have hfun : (fun N =>
      pathLawNorm q c - ‖compress (sectionSpaceC N) (atomCLMC q c)‖)
      = fun N => ‖atomCLMC q c‖ - ‖compress (sectionSpaceC N) (atomCLMC q c)‖ := by
    funext N
    rw [hTnorm]
  rw [hfun]
  exact h

end Cvs.PathLaw
