import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorFloor
import Cvs.L2a.ReflectionFloor
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mirror identity with a split, the defect `e₁`, and the P-weighted mirror floor

For a self-adjoint involution `J` and `h = u + a`: `‖h‖²/2 − ‖a‖² = ½‖u + Ja‖² + 2re⟨u,a⟩ + re⟨a,Ja⟩ − re⟨Jh + h, a⟩`.
On a rung span (Cvs.Prolate.RungExactOrthogonality, Cvs.Prolate.RungMirrorIdentity), `e₁ = calK(1_(1,∞)Φ) + 1_(1,∞)Φ` is `Σ aᵢ(1 − τᵢ)ψᵢ` on `(1, ∞)`, `Σ aᵢ(1 − τᵢ²)gᵢ/√(c/2π)`
on `(0, 1]`, and `∫₀^∞ |e₁|² = 2Σ aᵢ²(1 − τᵢ)Mᵢ`. an earlier result's floor with `D = −wΦ` and `FarFarBound`'s far-far bound (`MirrorConcentrationHalf`'s `ε_τ`)
give `∫₁^X Φ² ≥ (½ − ε/(2(2 − ε)) − η)∫_{Ioi 1} Φ²`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor

namespace Cvs.L2a.MirrorSplitDefect

/-! ### The abstract identities -/

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A self-adjoint involution preserves norms. -/
theorem norm_map_of_involution (J : E →ₗ[𝕜] E) (hsa : ∀ v w, ⟪J v, w⟫ = ⟪v, J w⟫) (hJJ : ∀ v, J (J v) = v)
    (v : E) : ‖J v‖ = ‖v‖ := by
  have h : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_self_eq_norm_sq (𝕜 := 𝕜), hsa, hJJ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **The mirror identity with a split (E4)**: for a self-adjoint involution `J` and `h = u + a`,
`‖h‖²/2 − ‖a‖² = ½‖u + Ja‖² + 2re⟨u, a⟩ + re⟨a, Ja⟩ − re⟨Jh + h, a⟩`. -/
theorem mirror_split (J : E →ₗ[𝕜] E) (hsa : ∀ v w, ⟪J v, w⟫ = ⟪v, J w⟫) (hJJ : ∀ v, J (J v) = v)
    (u a : E) :
    ‖u + a‖ ^ 2 / 2 - ‖a‖ ^ 2
      = ‖u + J a‖ ^ 2 / 2 + 2 * RCLike.re ⟪u, a⟫ + RCLike.re ⟪a, J a⟫
        - RCLike.re ⟪J (u + a) + (u + a), a⟫ := by
  have hJa := norm_map_of_involution J hsa hJJ a
  have e1 : ⟪J (u + a) + (u + a), a⟫ = ⟪u, J a⟫ + ⟪a, J a⟫ + ⟪u, a⟫ + ⟪a, a⟫ := by
    rw [map_add, inner_add_left, inner_add_left, inner_add_left, hsa u, hsa a]
    ring
  rw [e1, norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜), hJa, map_add, map_add, map_add,
    inner_self_eq_norm_sq (𝕜 := 𝕜)]
  ring

end Abstract

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-! ### The rung span in `L²(1, ∞)` and the transform of a cut rung -/

/-- `calK c` of a finite sum is the sum of the transforms, almost everywhere. -/
theorem calK_finsetSum {c : ℝ} (hc : 0 < c) {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i, MemLp (f i) 2 μ₀) :
    calK c (fun x => ∑ i ∈ s, f i x) =ᵐ[volume] fun y => ∑ i ∈ s, calK c (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := calK_smul hc (0 : ℂ) (memLp_ev (MemLp.zero : MemLp (0 : ℝ → ℂ) 2 μ₀))
      have e : (fun x : ℝ => ∑ i ∈ (∅ : Finset ι), f i x) = (0 : ℂ) • (0 : ℝ → ℂ) := by
        funext x; simp
      rw [e]
      filter_upwards [h0] with y hy
      rw [hy]; simp
  | insert i s hi ih =>
      have e : (fun x => ∑ j ∈ insert i s, f j x) = f i + fun x => ∑ j ∈ s, f j x := by
        funext x; simp [Finset.sum_insert hi]
      rw [e]
      filter_upwards [calK_add hc (memLp_ev (hf i)) (memLp_ev (memLp_finsetSum s fun j _ => hf j)), ih]
        with y h1 h2
      rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-- **The transform of a cut rung on `(0, ∞)`**: `calK c (1_(1,∞) ψ) = 1_[0,1] g/√(c/2π) − τψ` almost everywhere on
`(0, ∞)`, with `τ = μ√(c/2π)` (Cvs.Prolate.RungMirrorIdentity). -/
theorem calK_cut_rung {c μ : ℝ} {g : ℝ → ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    calK c ((Ioi 1).indicator fun x => (psi c g x : ℂ)) =ᵐ[μ₀]
      fun y => (((√(c / (2 * π)))⁻¹ * (Icc 0 1).indicator g y - μ * √(c / (2 * π)) * psi c g y : ℝ) : ℂ) := by
  set ψc : ℝ → ℂ := fun x => (psi c g x : ℂ) with hψc
  have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi hc hgc heven
  have hsplit : (Ioi 1).indicator ψc + (Iic 1).indicator ψc = ψc := by
    have := indicator_self_add_compl (Ioi (1 : ℝ)) ψc
    rwa [compl_Ioi] at this
  have hadd := calK_add hc (memLp_ev (hm.indicator (measurableSet_Ioi (a := (1 : ℝ))).nullMeasurableSet))
    (memLp_ev (hm.indicator (measurableSet_Iic (a := (1 : ℝ))).nullMeasurableSet))
  rw [hsplit] at hadd
  have ha : 0 < √(c / (2 * π)) := Real.sqrt_pos.2 (by positivity)
  set r : ℂ := (((√(c / (2 * π)))⁻¹ : ℝ) : ℂ) with hr
  have hψ : ψc =ᵐ[μ₀] r • calK c (fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (Cvs.Prolate.RungMirrorIdentity.calK_cut hc hgc heven)] with y hy
    rw [Pi.smul_apply, hy, smul_eq_mul, ← Complex.ofReal_mul, ← mul_assoc, inv_mul_cancel₀ ha.ne',
      one_mul]
  have hfull : calK c ψc =ᵐ[μ₀] r • fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ) := by
    rw [calK_congr hψ]
    have h1 := calK_smul hc r
      (memLp_ev_calK hc (memLp_ev (Cvs.Prolate.RungMirrorIdentity.memLp_cut_ofReal hgc)))
    have h2 := calK_calK hc (Cvs.Prolate.RungMirrorIdentity.memLp_cut_ofReal hgc)
    filter_upwards [ae_restrict_of_ae h1, h2] with y hy1 hy2
    rw [hy1, Pi.smul_apply, hy2, Pi.smul_apply]
  filter_upwards [ae_restrict_of_ae hadd, hfull,
    ae_restrict_of_ae (Cvs.Prolate.RungMirrorIdentity.calK_low hc hgc heven hμ)] with y h1 h2 h3
  rw [Pi.add_apply] at h1
  rw [Pi.smul_apply, smul_eq_mul] at h2
  rw [hr] at h2
  push_cast at h2 h3 ⊢
  linear_combination h2 - h1 - h3

/-- **The rung span in `L²(1, ∞)`**: classes `ψᵢ` of the rungs, pairwise orthogonal, with `Kψᵢ = −τᵢψᵢ` and
`‖ψᵢ‖² = Mᵢ`, and the class `F = Σ aᵢψᵢ` of `Φ` with `‖F‖² = ∫_{Ioi 1} Φ²` (Cvs.Prolate.RungExactOrthogonality, Cvs.Prolate.RungMirrorIdentity). -/
theorem rung_span_L2 {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∃ (ψL : ι → H₁) (F : H₁),
      (∀ i, (ψL i : ℝ → ℂ) =ᵐ[μ₁] fun x => (psi c (g i) x : ℂ))
      ∧ ((F : ℝ → ℂ) =ᵐ[μ₁] fun x => ((∑ i, a i * psi c (g i) x : ℝ) : ℂ))
      ∧ F = ∑ i, (a i : ℂ) • ψL i
      ∧ (∀ i, Kop hc (ψL i) = ((-(μ i * √(c / (2 * π))) : ℝ) : ℂ) • ψL i)
      ∧ (∀ i j, i ≠ j → inner ℂ (ψL i) (ψL j) = 0)
      ∧ (∀ i, ‖ψL i‖ ^ 2 = ∫ x in Ioi 1, psi c (g i) x ^ 2)
      ∧ ‖F‖ ^ 2 = ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  classical
  have hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1) := fun i => by
    have : ContinuousOn (g i) (uIcc (-1 : ℝ) 1) := fun s hs =>
      (hg i s hs).continuousAt.continuousWithinAt
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  set ψL : ι → H₁ := fun i => ((hψ i).ofReal (K := ℂ)).toLp fun x => (psi c (g i) x : ℂ) with hψL
  have hcoeψ : ∀ i, (ψL i : ℝ → ℂ) =ᵐ[μ₁] fun x => (psi c (g i) x : ℂ) := fun i =>
    MemLp.coeFn_toLp ((hψ i).ofReal (K := ℂ))
  have hsq0 : ∀ f : ℝ → ℝ, 0 ≤ ∫ x in Ioi 1, f x ^ 2 := fun f =>
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hFm : MemLp (fun x => ((∑ i, a i * psi c (g i) x : ℝ) : ℂ)) 2 μ₁ :=
    memLp_span Finset.univ hψ a
  refine ⟨ψL, hFm.toLp _, hcoeψ, hFm.coeFn_toLp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hψL]
    exact toLp_span Finset.univ hψ a
  · intro i
    have hcongr : calK c ((Ioi (1 : ℝ)).indicator (ψL i : ℝ → ℂ))
        = calK c ((Ioi 1).indicator fun x => (psi c (g i) x : ℂ)) :=
      calK_congr (ae_restrict_of_ae (indicator_congr (hcoeψ i)))
    refine Lp.ext ?_
    filter_upwards [coeFn_Kop hc (ψL i),
      Lp.coeFn_smul ((-(μ i * √(c / (2 * π))) : ℝ) : ℂ) (ψL i), hcoeψ i,
      Cvs.Prolate.RungMirrorIdentity.mirror_identity hc (hgc i) (heven i) (hμ i)] with y h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, h3, hcongr, h4, smul_eq_mul]
    push_cast; ring
  · intro i j hij
    rw [L2.inner_def]
    calc ∫ x, inner ℂ ((ψL i : ℝ → ℂ) x) ((ψL j : ℝ → ℂ) x) ∂μ₁
        = ∫ x in Ioi 1, ((psi c (g i) x * psi c (g j) x : ℝ) : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hcoeψ i, hcoeψ j] with x h1 h2
          rw [h1, h2, RCLike.inner_apply', Complex.conj_ofReal]; push_cast; ring
      _ = ((∫ x in Ioi 1, psi c (g i) x * psi c (g j) x : ℝ) : ℂ) := integral_ofReal
      _ = 0 := by
          rw [Cvs.Prolate.RungExactOrthogonality.integral_psi_mul_eq_zero (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j)
            (hg₁ j) (hg₂c j) (hang j) hc (hχ.ne hij), Complex.ofReal_zero]
  · intro i
    rw [hψL, norm_toLp_ofReal, Real.sq_sqrt (hsq0 _)]
  · rw [norm_toLp_ofReal, Real.sq_sqrt (hsq0 _)]

/-! ### The defect `e₁ = calK(1_(1,∞)Φ) + 1_(1,∞)Φ` on the rung span -/

/-- The extension by zero preserves norms: `‖ext h‖ = ‖h‖`, squared. -/
theorem norm_ext_sq (h : H₁) : ‖ext h‖ ^ 2 = ‖h‖ ^ 2 := by
  rw [norm_sq_eq_integral, norm_sq_eq_integral]
  calc ∫ x, ‖(ext h : ℝ → ℂ) x‖ ^ 2 ∂μ₀
      = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator (fun x => ‖(h : ℝ → ℂ) x‖ ^ 2) x := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_ext h] with x hx
        rw [hx]
        by_cases h1 : x ∈ Ioi (1 : ℝ)
        · rw [indicator_of_mem h1, indicator_of_mem h1]
        · rw [indicator_of_notMem h1, indicator_of_notMem h1, norm_zero]; ring
    _ = ∫ x in Ioi 1, ‖(h : ℝ → ℂ) x‖ ^ 2 := by
        rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- The defect `e₁ = calK c (1_(1,∞)Φ) + 1_(1,∞)Φ` of a real `Φ`. -/
def eOne (c : ℝ) (Φ : ℝ → ℝ) : ℝ → ℂ := fun y =>
  calK c ((Ioi 1).indicator fun x => (Φ x : ℂ)) y + (Ioi 1).indicator (fun x => (Φ x : ℂ)) y

/-- **`e₁` on the rung span**, almost everywhere on `(0, ∞)`: `e₁ = Σ aᵢ(1_[0,1] gᵢ/√(c/2π) − τᵢψᵢ + 1_(1,∞)ψᵢ)`,
with `τᵢ = μᵢ√(c/2π)`. -/
theorem eOne_ae_eq {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {c : ℝ} {μ : ι → ℝ} (a : ι → ℝ) (hc : 0 < c)
    (hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1)) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) =ᵐ[μ₀] fun y =>
      ((∑ i, a i * ((√(c / (2 * π)))⁻¹ * (Icc 0 1).indicator (g i) y
        - μ i * √(c / (2 * π)) * psi c (g i) y + (Ioi 1).indicator (psi c (g i)) y) : ℝ) : ℂ) := by
  classical
  have hm : ∀ i, MemLp (fun x => (psi c (g i) x : ℂ)) 2 μ₀ := fun i =>
    Cvs.Prolate.RungMirrorIdentity.memLp_psi hc (hgc i) (heven i)
  set fi : ι → ℝ → ℂ := fun i => (a i : ℂ) • (Ioi 1).indicator fun x => (psi c (g i) x : ℂ) with hfi
  have hind : ((Ioi 1).indicator fun x => ((∑ i, a i * psi c (g i) x : ℝ) : ℂ)) = fun x => ∑ i, fi i x := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [hfi, indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]; push_cast; rfl
    · simp [hfi, indicator_of_notMem hx]
  have hsum := calK_finsetSum hc Finset.univ (f := fi)
    (fun i => ((hm i).indicator measurableSet_Ioi.nullMeasurableSet).const_smul _)
  have hall : ∀ᵐ y ∂μ₀, ∀ i, calK c (fi i) y = (a i : ℂ) *
      (((√(c / (2 * π)))⁻¹ * (Icc 0 1).indicator (g i) y - μ i * √(c / (2 * π)) * psi c (g i) y : ℝ) : ℂ) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ae_restrict_of_ae (calK_smul hc (a i : ℂ) (memLp_ev ((hm i).indicator measurableSet_Ioi.nullMeasurableSet))),
      calK_cut_rung hc (hgc i) (heven i) (hμ i)] with y h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  unfold eOne
  beta_reduce
  rw [hind]
  filter_upwards [ae_restrict_of_ae hsum, hall] with y h1 h2
  rw [h1]
  simp only [h2]
  rw [← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hfi, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem hy, indicator_of_mem hy]; push_cast; ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]; push_cast; ring

/-- **`e₁` on `(1, ∞)`**: `e₁ = Σ aᵢ(1 − τᵢ)ψᵢ` almost everywhere, with `τᵢ = μᵢ√(c/2π)`. -/
theorem eOne_high {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {c : ℝ} {μ : ι → ℝ} (a : ι → ℝ) (hc : 0 < c)
    (hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1)) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∀ᵐ y ∂μ₁, eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) y
      = ((∑ i, a i * (1 - μ i * √(c / (2 * π))) * psi c (g i) y : ℝ) : ℂ) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one)
    (eOne_ae_eq a hc hgc heven hμ), ae_restrict_mem measurableSet_Ioi] with y h1 hy
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hy' : y ∉ Icc (0 : ℝ) 1 := fun h => (not_le.2 (show (1 : ℝ) < y from hy)) h.2
  rw [indicator_of_notMem hy', indicator_of_mem hy]
  ring

/-! ### The P-weighted mirror floor on the rung span (Theorem 1) -/

/-- Multiplication by a real weight is self-adjoint on `L²(1, ∞)`. -/
theorem inner_Wop {w : ℝ → ℝ} (hwm : Measurable w) (hw : ∀ x, |w x| ≤ 1) (f k : H₁) :
    inner ℂ (Wop hwm hw f) k = inner ℂ f (Wop hwm hw k) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_weight hwm hw (Lp.memLp f)).coeFn_toLp,
    (memLp_weight hwm hw (Lp.memLp k)).coeFn_toLp] with x h1 h2
  change inner ℂ (((memLp_weight hwm hw (Lp.memLp f)).toLp _ : ℝ → ℂ) x) ((k : ℝ → ℂ) x)
    = inner ℂ ((f : ℝ → ℂ) x) (((memLp_weight hwm hw (Lp.memLp k)).toLp _ : ℝ → ℂ) x)
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

end Cvs.L2a.MirrorSplitDefect
