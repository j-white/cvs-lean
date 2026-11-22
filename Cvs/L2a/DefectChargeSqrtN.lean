import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.MirrorSplitDefect
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ReflectionFloor
import Cvs.Prolate.RungExactOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `e₁` charge through `√N`

On `(1, ∞)` the dilate sum is `E = posTail Φ X − 1_(1,X]Φ` (Cvs.L2a.CoreArmIdentity), so `‖E‖ ≤ √N + √P` with `N = ∫_{Ioi 1} posTail²`.
With `‖e₁‖_{L²(1,∞)} ≤ ε√P` (Cvs.L2a.CleanBandDilation) this gives `|2re⟨e₁, E⟩| ≤ 2ε(√P√N + P)` on the rung span, for every `X`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.ReflectionFloor Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.CleanBandDilation

namespace Cvs.L2a.DefectChargeSqrtN

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-- **Minkowski on the tail split**: `‖E‖ ≤ √N + √P` for the class `e` of `E = dilSum Φ X`, with
`N = ∫_{Ioi 1} (posTail Φ X)²` and `P = ∫_{Ioi 1} Φ²`. -/
theorem norm_dilSum_le_sqrt {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 μ₁) (X : ℝ) {e : H₀}
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    ‖e‖ ≤ √(∫ θ in Ioi 1, posTail Φ X θ ^ 2) + √(∫ ξ in Ioi 1, Φ ξ ^ 2) := by
  have hcut : MemLp (fun x => (((Ioc 1 X).indicator Φ x : ℝ) : ℂ)) 2 μ₀ := by
    simpa using memLp_cut hΦ X (m := 1) le_rfl
  set r : H₀ := hcut.toLp _ with hr
  have hrae : (r : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator Φ x : ℝ) : ℂ) := hcut.coeFn_toLp
  have hqae : ((e + r : H₀) : ℝ → ℂ) =ᵐ[μ₀] fun x => ((posTail Φ X x : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_add e r, he, hrae] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, posTail_eq_add_dilSum, Complex.ofReal_add, add_comm]
  have hcut0 : ∀ x, x ≤ 1 → (Ioc 1 X).indicator Φ x = 0 := fun x hx =>
    indicator_of_notMem (fun (h : x ∈ Ioc 1 X) => not_lt.2 hx h.1) _
  have hpos0 : ∀ x, x ≤ 1 → posTail Φ X x = 0 := fun x hx => by
    rw [posTail_eq_add_dilSum, hcut0 x hx, dilSum_of_le_one hx, add_zero]
  have hq := norm_sq_of_ae hqae hpos0
  have hr2 := norm_sq_of_ae hrae hcut0
  have hrP : ∫ x in Ioi 1, (Ioc 1 X).indicator Φ x ^ 2 ≤ ∫ ξ in Ioi 1, Φ ξ ^ 2 := by
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
      ((memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).1 hΦ) (ae_of_all _ fun x => ?_)
    dsimp only
    by_cases hx : x ∈ Ioc 1 X
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, zero_pow two_ne_zero]; exact sq_nonneg _
  have hqn : ‖e + r‖ = √(∫ θ in Ioi 1, posTail Φ X θ ^ 2) := by
    rw [← hq, Real.sqrt_sq (norm_nonneg _)]
  have hrn : ‖r‖ ≤ √(∫ ξ in Ioi 1, Φ ξ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg r), hr2]
    exact Real.sqrt_le_sqrt hrP
  calc ‖e‖ = ‖(e + r) - r‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖e + r‖ + ‖r‖ := norm_sub_le _ _
    _ ≤ _ := by rw [hqn]; linarith

/-- **N1, the `e₁` charge through `√N`**: on the rung span with `1 − ε ≤ τᵢ`,
`|2re⟨e₁, E⟩| ≤ 2ε(√P√N + P)` for every `X`, with `P = ∫_{Ioi 1} Φ²` and `N = ∫_{Ioi 1} (posTail Φ X)²`. -/
theorem eone_charge_sqrtN {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ}
    {χ μ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π))) (X : ℝ) {h e : H₀}
    (hh : (h : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum (fun ξ => ∑ i, a i * psi c (g i) ξ) X x : ℝ) : ℂ)) :
    |2 * RCLike.re (inner ℂ (Uop hc h + h) e)|
      ≤ 2 * ε * (√(∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
          * √(∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
        + ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ
  have hΦr : MemLp Φ 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have he0 : ∀ᵐ x ∂μ₀, x ≤ 1 → (e : ℝ → ℂ) x = 0 := by
    filter_upwards [he] with x hx hx1
    rw [hx, dilSum_of_le_one hx1, Complex.ofReal_zero]
  have h1 := abs_re_inner_le_of_ae_zero (f := Uop hc h + h) he0
  have h2 : ∫ y in Ioi 1, ‖((Uop hc h + h : H₀) : ℝ → ℂ) y‖ ^ 2 = ∫ y in Ioi 1, ‖eOne c Φ y‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) (eOne_ae_of_ae hc hh)]
      with y hy
    rw [hy]
  have h3 := integral_norm_eOne_sq_Ioi_one_le a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ
  have h4 := norm_dilSum_le_sqrt hΦr X he
  have hP : 0 ≤ ∫ ξ in Ioi 1, Φ ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h5 : √(∫ y in Ioi 1, ‖((Uop hc h + h : H₀) : ℝ → ℂ) y‖ ^ 2) ≤ ε * √(∫ ξ in Ioi 1, Φ ξ ^ 2) := by
    rw [h2, ← Real.sqrt_sq hε, ← Real.sqrt_mul' _ hP]
    exact Real.sqrt_le_sqrt h3
  have h6 := mul_le_mul h5 h4 (norm_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _))
  have h7 := Real.mul_self_sqrt hP
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |RCLike.re (inner ℂ (Uop hc h + h) e)|
      ≤ 2 * (ε * √(∫ ξ in Ioi 1, Φ ξ ^ 2)
          * (√(∫ θ in Ioi 1, posTail Φ X θ ^ 2) + √(∫ ξ in Ioi 1, Φ ξ ^ 2))) := by
        linarith
    _ = 2 * ε * (√(∫ ξ in Ioi 1, Φ ξ ^ 2) * √(∫ θ in Ioi 1, posTail Φ X θ ^ 2)
          + √(∫ ξ in Ioi 1, Φ ξ ^ 2) * √(∫ ξ in Ioi 1, Φ ξ ^ 2)) := by ring
    _ = _ := by rw [h7]

end Cvs.L2a.DefectChargeSqrtN
