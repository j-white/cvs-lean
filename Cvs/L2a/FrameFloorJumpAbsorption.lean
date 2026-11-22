import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.FrameFloorMirror
import Cvs.L2a.MirrorFloor
import Cvs.L2a.MirrorSplitDefect
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ReflectionFloor
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frame floor from jump absorption

`CoreArmIdentity`'s core/arm identity reads `N − P/2 = Pos + re⟨a, Ja⟩ − re⟨e₁, a⟩ + Dil`. If `Dil ≥ −θ·Pos − r·P` with `θ ≤ 1`,
then on a rung span `N ≥ (½ − ε − η − r)P`: `ε` bounds `e₁` on `(1, ∞)` (Cvs.L2a.MirrorSplitDefect, Cvs.L2a.MirrorConcentrationHalf) and `η` is `FarFarBound`'s far-far
constant. With Cvs.L2a.FrameFloorMirror this is the frame floor `κ_F Σ aᵢ²∫₁^X ψᵢ² ≤ N`, and `PositionTailSpanAdapters`'s `FR_of_FF` gives the window bound.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity

namespace Cvs.L2a.FrameFloorJumpAbsorption

/-! ### The defect on an eigenvector span -/

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **The defect on a span**: for a contraction `K` with orthogonal eigenvectors `Kψᵢ = −τᵢψᵢ`, `1 − ε ≤ τᵢ` and
`0 ≤ ε`: `‖KΦ + Φ‖ ≤ ε‖Φ‖` for `Φ = Σ bᵢψᵢ`. -/
theorem norm_map_add_self_le {ι : Type*} [Fintype ι] (K : E →ₗ[𝕜] E) (hK : ∀ v, ‖K v‖ ≤ ‖v‖) {ψ : ι → E}
    (horth : ∀ i j, i ≠ j → ⟪ψ i, ψ j⟫ = 0) {τ : ι → ℝ} (hKψ : ∀ i, K (ψ i) = ((-τ i : ℝ) : 𝕜) • ψ i)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ τ i) (b : ι → 𝕜) :
    ‖K (∑ i, b i • ψ i) + ∑ i, b i • ψ i‖ ≤ ε * ‖∑ i, b i • ψ i‖ := by
  have hsum : K (∑ i, b i • ψ i) + ∑ i, b i • ψ i = ∑ i, (b i * ((1 - τ i : ℝ) : 𝕜)) • ψ i := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hKψ, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hτ1 : ∀ i, ψ i ≠ 0 → τ i ≤ 1 := fun i hi => by
    have h := hK (ψ i)
    rw [hKψ, norm_smul, RCLike.norm_ofReal, abs_neg] at h
    have hp : 0 < ‖ψ i‖ := norm_pos_iff.2 hi
    have h' : |τ i| ≤ 1 := le_of_mul_le_mul_right (by linarith) hp
    exact (le_abs_self _).trans h'
  have hsq : ‖K (∑ i, b i • ψ i) + ∑ i, b i • ψ i‖ ^ 2 ≤ (ε * ‖∑ i, b i • ψ i‖) ^ 2 := by
    rw [hsum, mul_pow, norm_sum_smul_orth_sq horth, norm_sum_smul_orth_sq horth, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
    by_cases hi : ψ i = 0
    · simp [hi]
    · have h1 : (1 - τ i) ^ 2 ≤ ε ^ 2 := by
        have := hτ1 i hi
        have := hτ i
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg ‖b i‖) (sq_nonneg ‖ψ i‖))
      linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _)) two_ne_zero).1 hsq

end Abstract

/-! ### `Pos` and `Dil` as integrals -/

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-- **`Pos`** of the core/arm identity: `½‖u + J(χh)‖² + 2∫ χ(1 − χ)Φ² + ‖E − J(1_(1,X]χΦ)‖²`, with `J = calK c`,
`u = 1_(1,∞)(1 − χ)Φ`, `h = 1_(1,∞)Φ` and `E = dilSum Φ X`. -/
def corePos (c : ℝ) (Φ χ : ℝ → ℝ) (X : ℝ) : ℝ :=
  (∫ y in Ioi 0, ‖(((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) y : ℝ) : ℂ)
      + calK c (fun x => (((Ioi 1).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y‖ ^ 2) / 2
    + 2 * (∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2)
    + ∫ y in Ioi 0, ‖((dilSum Φ X y : ℝ) : ℂ)
      - calK c (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y‖ ^ 2

/-- **`Dil`** of the core/arm identity: `2∫_{Ioi 1} (1_(1,X]Φ + re J(1_(1,X]χΦ)) · E`, with `J = calK c` and
`E = dilSum Φ X`. -/
def coreDil (c : ℝ) (Φ χ : ℝ → ℝ) (X : ℝ) : ℝ :=
  2 * ∫ y in Ioi 1, ((Ioc 1 X).indicator Φ y
    + (calK c (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y).re) * dilSum Φ X y

/-- `Pos` of `CoreArmIdentity`'s `core_arm_identity_L2`, written through the classes of the pieces, is `corePos`. -/
theorem corePos_eq {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    ‖u + Uop hc (aB + aF)‖ ^ 2 / 2 + 2 * (∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2) + ‖e - Uop hc aB‖ ^ 2
      = corePos c Φ χ X := by
  obtain ⟨-, ha, -, -, -⟩ := core_arm_ae hX hχX hu haB haF he
  have h1 : ‖u + Uop hc (aB + aF)‖ ^ 2 = ∫ y in Ioi 0, ‖(((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) y : ℝ) : ℂ)
      + calK c (fun x => (((Ioi 1).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u (Uop hc (aB + aF)), hu, coeFn_Uop hc (aB + aF)] with y h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, calK_congr ha]
  have h2 : ‖e - Uop hc aB‖ ^ 2 = ∫ y in Ioi 0, ‖((dilSum Φ X y : ℝ) : ℂ)
      - calK c (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub e (Uop hc aB), he, coeFn_Uop hc aB] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, calK_congr haB]
  rw [h1, h2]
  rfl

/-- `Dil` of `CoreArmIdentity`'s `core_arm_identity_L2`, `2re⟨u + a_B + Ja_B, e⟩`, is `coreDil`. -/
theorem coreDil_eq {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    2 * RCLike.re (inner ℂ (u + aB + Uop hc aB) e) = coreDil c Φ χ X := by
  obtain ⟨-, -, huB, -, -⟩ := core_arm_ae hX hχX hu haB haF he
  have h : RCLike.re (inner ℂ (u + aB + Uop hc aB) e) = ∫ y in Ioi 0, ((Ioc 1 X).indicator Φ y
      + (calK c (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) y).re) * dilSum Φ X y := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (u + aB) (Uop hc aB), huB, coeFn_Uop hc aB, he] with y h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, h4, calK_congr haB, RCLike.inner_apply']
    simp
  rw [h, integral_Ioi_zero_eq fun x hx => by rw [dilSum_of_le_one hx, mul_zero]]
  rfl

/-! ### The floor from jump absorption -/

/-- **Jump absorption gives the half floor**: with `CoreArmIdentity`'s pieces, `0 ≤ χ ≤ 1` on `(1, ∞)`, `θ ≤ 1` and
`Dil ≥ −θ·Pos − r·P`: `re⟨a, Ja⟩ − re⟨e₁, a⟩ − rP ≤ N − P/2`, where `h = u + a`, `a = a_B + a_F`, `e₁ = Jh + h`. -/
theorem half_le_of_absorption {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) (hχ01 : ∀ x, 1 < x → 0 ≤ χ x ∧ χ x ≤ 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) {θ r : ℝ} (hθ : θ ≤ 1)
    (hAL : -θ * corePos c Φ χ X - r * (∫ ξ in Ioi 1, Φ ξ ^ 2) ≤ coreDil c Φ χ X) :
    RCLike.re (inner ℂ (aB + aF) (Uop hc (aB + aF)))
        - RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) (aB + aF))
        - r * (∫ ξ in Ioi 1, Φ ξ ^ 2)
      ≤ (∫ y in Ioi 1, posTail Φ X y ^ 2) - (∫ ξ in Ioi 1, Φ ξ ^ 2) / 2 := by
  have hid := core_arm_identity_L2 hc hX hχX hu haB haF he
  have hP := corePos_eq hc hX hχX hu haB haF he
  have hD := coreDil_eq hc hX hχX hu haB haF he
  have hpos := pos_nonneg (Φ := Φ) hχ01 (u + Uop hc (aB + aF)) (e - Uop hc aB)
  rw [hP] at hpos
  have hθP := mul_nonneg (sub_nonneg.2 hθ) hpos
  linarith

/-- The inner product of two extensions by zero is the inner product in `L²(1, ∞)`. -/
theorem inner_ext (f g : H₁) : inner ℂ (ext f) (ext g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  calc ∫ x, inner ℂ ((ext f : ℝ → ℂ) x) ((ext g : ℝ → ℂ) x) ∂μ₀
      = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator (fun x => inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x)) x := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_ext f, coeFn_ext g] with x h1 h2
        rw [h1, h2]
        by_cases hx : x ∈ Ioi (1 : ℝ)
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]
    _ = ∫ x in Ioi 1, inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x) := integral_Ioi_zero_indicator _

/-- A real indicator cast to `ℂ` is the indicator of the cast. -/
theorem ofReal_indicator (s : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ((s.indicator f x : ℝ) : ℂ) = s.indicator (fun x => (f x : ℂ)) x := by
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, Complex.ofReal_zero]

/-- **The floor from jump absorption on the rung span**: for even rungs with distinct `χᵢ`, `1 − ε ≤ τᵢ`, `0 ≤ ε`,
a weight `0 ≤ w ≤ 1` equal to `1` beyond `X ≥ 1`, `MirrorSplitDefect`'s `η` bound and `Dil ≥ −θ·Pos − r·P` with `θ ≤ 1`:
`(½ − ε − η − r) P ≤ N`, with `P = ∫_{Ioi 1} Φ²` and `N = ∫_{Ioi 1} (posTail Φ X)²`. -/
theorem floor_of_absorption {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {θ r : ℝ} (hθ : θ ≤ 1)
    (hAL : -θ * corePos c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X
        - r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ coreDil c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X) :
    (1 / 2 - ε - η - r) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 := by
  classical
  obtain ⟨ψL, F, -, hF, hFsum, hKψ, horth, -, hF2⟩ := rung_span_L2 a hg hg₁ hg₂c hang hc hχ heven hμ
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  have hΦr : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ => (hψ i).const_mul (a i)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun ξ => ∑ i, a i * psi c (g i) ξ := ⟨_, rfl⟩
  rw [← hΦdef] at hAL hΦr ⊢
  have key : ∀ ξ, ∑ i, a i * psi c (g i) ξ = Φ ξ := fun ξ => by rw [hΦdef]
  simp only [key] at hη hF hF2 hAL ⊢
  have hw : ∀ x, |w x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hw0 x], hw1 x⟩
  obtain ⟨u, aB, aF, e, hu, haB, haF, he⟩ := exists_core_arm hX hΦr hwm hw0 hw1
  have hmain := half_le_of_absorption hc hX hwX (fun x _ => ⟨hw0 x, hw1 x⟩) hu haB haF he hθ hAL
  obtain ⟨hh, ha, -, -, -⟩ := core_arm_ae hX hwX hu haB haF he
  have hWF : ((Wop hwm hw F : H₁) : ℝ → ℂ) =ᵐ[μ₁] fun x => ((w x * Φ x : ℝ) : ℂ) := by
    filter_upwards [(memLp_weight hwm hw (Lp.memLp F)).coeFn_toLp, hF] with x h1 h2
    change ((memLp_weight hwm hw (Lp.memLp F)).toLp _ : ℝ → ℂ) x = _
    rw [h1, h2]; push_cast; ring
  -- `h = ext F` and `a = ext (W F)`
  have hhe : u + (aB + aF) = ext F := by
    refine Lp.ext ?_
    filter_upwards [hh, coeFn_ext F, ae_restrict_of_ae (indicator_congr hF)] with y h1 h2 h3
    rw [h1, h2, h3, ofReal_indicator]
  have hae : aB + aF = ext (Wop hwm hw F) := by
    refine Lp.ext ?_
    filter_upwards [ha, coeFn_ext (Wop hwm hw F), ae_restrict_of_ae (indicator_congr hWF)] with y h1 h2 h3
    rw [h1, h2, h3, ofReal_indicator]
  rw [hhe, hae] at hmain
  -- the `η` term: `re⟨a, Ja⟩ ≥ −ηP`
  have hη' : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ≤ η * ‖F‖ := by
    have hcongr : calK c ((Ioi (1 : ℝ)).indicator (Wop hwm hw F : ℝ → ℂ))
        = calK c ((Ioi 1).indicator fun x => ((w x * Φ x : ℝ) : ℂ)) :=
      calK_congr (ae_restrict_of_ae (indicator_congr hWF))
    have hsq : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ^ 2 ≤ (η * ‖F‖) ^ 2 := by
      rw [mul_pow, hF2, norm_sq_eq_integral]
      refine le_of_eq_of_le (integral_congr_ae ?_) hη
      filter_upwards [(memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).coeFn_toLp,
        (memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).coeFn_toLp] with y h1 h2
      change ‖((memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h1]
      change ‖(w y : ℂ) * ((memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h2, hcongr]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hη0 (norm_nonneg _))
      two_ne_zero).1 hsq
  have hJa : -(η * ‖F‖ ^ 2) ≤ RCLike.re (inner ℂ (ext (Wop hwm hw F)) (Uop hc (ext (Wop hwm hw F)))) := by
    rw [← inner_Kop_right, inner_Wop]
    have h1 := RCLike.abs_re_le_norm (inner ℂ F (Wop hwm hw (Kop hc (Wop hwm hw F))))
    have h2 := norm_inner_le_norm (𝕜 := ℂ) F (Wop hwm hw (Kop hc (Wop hwm hw F)))
    have h3 := mul_le_mul_of_nonneg_left hη' (norm_nonneg F)
    have h4 := neg_abs_le (RCLike.re (inner ℂ F (Wop hwm hw (Kop hc (Wop hwm hw F)))))
    nlinarith
  -- the `e₁` term: `re⟨e₁, a⟩ ≤ εP`
  have he1 : RCLike.re (inner ℂ (Uop hc (ext F) + ext F) (ext (Wop hwm hw F))) ≤ ε * ‖F‖ ^ 2 := by
    rw [inner_add_left, ← inner_Kop_left, inner_ext, ← inner_add_left]
    have hK := norm_map_add_self_le (Kop hc) (norm_Kop_le hc) horth (τ := fun i => μ i * √(c / (2 * π)))
      hKψ hε hτ (fun i => (a i : ℂ))
    rw [← hFsum] at hK
    have h1 := RCLike.re_le_norm (inner ℂ (Kop hc F + F) (Wop hwm hw F))
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (Kop hc F + F) (Wop hwm hw F)
    have h3 := mul_le_mul hK (norm_Wop_le hwm hw F) (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))
    nlinarith
  rw [← hF2] at hmain ⊢
  have hexp : (1 / 2 - ε - η - r) * ‖F‖ ^ 2 = ‖F‖ ^ 2 / 2 - ε * ‖F‖ ^ 2 - η * ‖F‖ ^ 2 - r * ‖F‖ ^ 2 := by ring
  linarith

/-- **Masses below a floor**: from `κP ≤ N` with `N ≥ 0`, `κ Σ aᵢ²∫₁^X ψᵢ² ≤ N` for any real `κ` (Cvs.L2a.FrameFloorMirror). -/
theorem FF_of_floor {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {X κ N : ℝ} (hX : 1 ≤ X) (hN : 0 ≤ N)
    (hfloor : κ * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 ≤ N) :
    κ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) ≤ N := by
  have hS0 : 0 ≤ ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (intervalIntegral.integral_nonneg hX fun _ _ => sq_nonneg _)
  rcases le_or_gt 0 κ with hκ | hκ
  · exact (mul_le_mul_of_nonneg_left (Cvs.L2a.FrameFloorMirror.sum_mass_le_full a hg hg₁ hg₂c hang hc hχ hX)
      hκ).trans hfloor
  · exact (mul_nonpos_of_nonpos_of_nonneg hκ.le hS0).trans hN

end Cvs.L2a.FrameFloorJumpAbsorption
