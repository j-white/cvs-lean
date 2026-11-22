import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorFloor
import Cvs.L2a.OdeFreeFrames
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
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
# The frame floor from the mirror

For `Φ = Σ aᵢψᵢ` on distinct rungs, exact orthogonality (Cvs.Prolate.RungExactOrthogonality) gives `Σ aᵢ²∫₁^X ψᵢ² ≤ ∫_{Ioi 1} Φ²`; with the mirror
floor `μ_β ∫_{Ioi 1} Φ² ≤ ∫₁^X Φ²` (Cvs.L2a.MirrorFloor) and a frame `∫₁^X Φ² ≤ K·N` (Cvs.L2a.OdeFreeFrames) this is the floor
`(μ_β/K) Σ aᵢ²∫₁^X ψᵢ² ≤ N = ∫_{Ioi 1} (posTail Φ X)²`, with `K = 16.31` for `1 ≤ X < 9`, `2` on `[2, 3]` and
`3.3515` on `[3, 4]`; `μ_β > 0` for `0 ≤ β < 1`, so it is `RungSpanPole`'s `hFF` with `κF = μ_β/K`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine
open Cvs.L2a.MirrorFloor (muBeta)

namespace Cvs.L2a.FrameFloorMirror

/-- The mirror floor constant is positive: `0 < μ_β` for `0 ≤ β < 1`. -/
theorem muBeta_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : 0 < muBeta β := by
  unfold muBeta
  have hlt : β < √(2 - β ^ 2) := (Real.lt_sqrt hβ0).mpr (by nlinarith)
  have : 0 < (√(2 - β ^ 2) - β) / 2 := by linarith
  positivity

/-- **Masses below the full mass**: for distinct rungs and `1 ≤ X`, `Σ aᵢ²∫₁^X ψᵢ² ≤ ∫_{Ioi 1} (Σ aᵢψᵢ)²`. -/
theorem sum_mass_le_full {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {X : ℝ} (hX : 1 ≤ X) :
    ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hint : IntegrableOn (fun ξ => psi c (g i) ξ ^ 2) (Ioi 1) :=
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).integrable_sq
  rw [intervalIntegral.integral_of_le hX]
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    (Filter.Eventually.of_forall Ioc_subset_Ioi_self)

/-- **Floor plus frame**: from `μ ∫_{Ioi 1} Φ² ≤ ∫₁^X Φ²` and `∫₁^X Φ² ≤ K·N` with `0 ≤ μ`, `0 < K`,
`(μ/K) Σ aᵢ²∫₁^X ψᵢ² ≤ N`. -/
theorem FF_of_floor {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {X μ K N : ℝ} (hX : 1 ≤ X) (hμ : 0 ≤ μ) (hK : 0 < K)
    (hfloor : μ * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ ∫ ξ in (1 : ℝ)..X, (∑ i, a i * psi c (g i) ξ) ^ 2)
    (hframe : ∫ ξ in (1 : ℝ)..X, (∑ i, a i * psi c (g i) ξ) ^ 2 ≤ K * N) :
    μ / K * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) ≤ N := by
  have hS := sum_mass_le_full a hg hg₁ hg₂c hang hc hχ hX
  have h1 : μ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) ≤ K * N :=
    ((mul_le_mul_of_nonneg_left hS hμ).trans hfloor).trans hframe
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  linarith

/-- **The frame floor from the mirror**: under the hypotheses of `MirrorFloor`'s `mirror_floor_span` and a frame
`∫₁^X Φ² ≤ K·N`, `(μ_{η+ε}/K) Σ aᵢ²∫₁^X ψᵢ² ≤ N` with `N = ∫_{Ioi 1} (posTail Φ X)²`. -/
theorem FF_of_mirror {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
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
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X ≤ x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    (hβ : η + ε < 1) {K : ℝ} (hK : 0 < K)
    (hframe : ∫ ξ in (1 : ℝ)..X, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ K * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    muBeta (η + ε) / K * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
  FF_of_floor a hg hg₁ hg₂c hang hc hχ hX (muBeta_pos (by linarith) hβ).le hK
    (Cvs.L2a.MirrorFloor.mirror_floor_span a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ hwm hw0 hw1 hX hwX
      hη0 hη hβ) hframe

/-- The rung span is continuous on `[1, X]`. -/
theorem continuousOn_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0) (X : ℝ) :
    ContinuousOn (fun ξ => ∑ i, a i * psi c (g i) ξ) (Icc 1 X) :=
  (continuous_finsetSum _ fun i _ => continuous_const.mul
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1).continuousOn

/-- **The mirror floor below `9`**: for `1 ≤ X < 9`, `(μ_{η+ε}/16.31) Σ aᵢ²∫₁^X ψᵢ² ≤ N`. -/
theorem FF_mirror_lt_nine {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
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
    {X : ℝ} (hX : 1 ≤ X) (hX9 : X < 9) (hwX : ∀ x, X ≤ x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    (hβ : η + ε < 1) :
    muBeta (η + ε) / 16.31 * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
  FF_of_mirror a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ hwm hw0 hw1 hX hwX hη0 hη hβ (by norm_num)
    (Cvs.L2a.OdeFreeFrames.frame_moebius_lt_nine hX hX9
      (Cvs.L2a.OdeFreeFrames.integrableOn_of_continuousOn (continuousOn_span a hg hg₁ hg₂c hang X)).2)

end Cvs.L2a.FrameFloorMirror
