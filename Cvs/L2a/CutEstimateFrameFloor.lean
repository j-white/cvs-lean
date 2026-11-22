import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutPointCountForm
import Cvs.L2a.CutPointReduction
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.PositionTruncatedTail
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut estimate from a frame floor

B0 in count form, `|cutNS| ≤ (6J/c)(Λ°(X) + κ(X))·Σ aᵢ²∫₁^X ψᵢ²`, so any floor `κ_P Σ aᵢ²∫₁^X ψᵢ² ≤ N` gives `PositionTailFullTail`'s `hNS`
with `ε_c = 0` and `C = (6J/c)(Λ°(X) + κ(X))/κ_P`. With the `sin²` ramp `ω = log θ · ramp(5/4, 1/4)` of Cvs.Upstream.SineSquaredRamp this is
Cvs.L2a.PositionTailFullTail with `hNS` and its weight hypotheses discharged.
-/

namespace Cvs.L2a.CutEstimateFrameFloor

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.CutWeightResidual Cvs.L2a.CutGap Cvs.L2a.CutPointReduction Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- The NS cut weight `ω(θ) = log θ · ramp(5/4, 1/4)(θ)`: `0` up to `5/4`, `log θ` from `3/2`. -/
noncomputable def nsRamp (θ : ℝ) : ℝ := Real.log θ * Cvs.Upstream.SineSquaredRamp.ramp (5 / 4) (1 / 4) θ

/-- Its derivative on `θ > 0`. -/
noncomputable def nsRamp' (θ : ℝ) : ℝ :=
  Cvs.Upstream.SineSquaredRamp.ramp (5 / 4) (1 / 4) θ / θ
    + Real.log θ * Cvs.Upstream.SineSquaredRamp.ramp' (5 / 4) (1 / 4) θ

theorem nsRamp_of_le {θ : ℝ} (hθ : θ ≤ 5 / 4) : nsRamp θ = 0 := by
  unfold nsRamp; rw [Cvs.Upstream.SineSquaredRamp.ramp_of_le hθ, mul_zero]

theorem nsRamp_of_ge {θ : ℝ} (hθ : 3 / 2 ≤ θ) : nsRamp θ = Real.log θ := by
  unfold nsRamp
  rw [Cvs.Upstream.SineSquaredRamp.ramp_of_ge (by norm_num) (by linarith), mul_one]

theorem nsRamp_nonneg {θ : ℝ} (hθ : 1 ≤ θ) : 0 ≤ nsRamp θ :=
  mul_nonneg (Real.log_nonneg hθ) (Cvs.Upstream.SineSquaredRamp.ramp_nonneg _ _ _)

theorem nsRamp_le_log {θ : ℝ} (hθ : 1 ≤ θ) : nsRamp θ ≤ Real.log θ :=
  mul_le_of_le_one_right (Real.log_nonneg hθ) (Cvs.Upstream.SineSquaredRamp.ramp_le_one _ _ _)

theorem hasDerivAt_nsRamp {θ : ℝ} (hθ : 0 < θ) : HasDerivAt nsRamp (nsRamp' θ) θ := by
  have h := (Real.hasDerivAt_log hθ.ne').mul
    (Cvs.Upstream.SineSquaredRamp.hasDerivAt_ramp (a := 5 / 4) (h := 1 / 4) (by norm_num) θ)
  have e : nsRamp' θ = θ⁻¹ * Cvs.Upstream.SineSquaredRamp.ramp (5 / 4) (1 / 4) θ
      + Real.log θ * Cvs.Upstream.SineSquaredRamp.ramp' (5 / 4) (1 / 4) θ := by
    unfold nsRamp'; rw [div_eq_inv_mul]
  rw [e]
  exact h

theorem continuousOn_nsRamp' : ContinuousOn nsRamp' (Ioi 0) := by
  have hr : Continuous (Cvs.Upstream.SineSquaredRamp.ramp (5 / 4) (1 / 4)) :=
    continuous_iff_continuousAt.2 fun θ =>
      (Cvs.Upstream.SineSquaredRamp.hasDerivAt_ramp (a := 5 / 4) (h := 1 / 4) (by norm_num) θ).continuousAt
  have hr' := Cvs.Upstream.SineSquaredRamp.continuous_ramp' (a := 5 / 4) (h := 1 / 4) (by norm_num)
  unfold nsRamp'
  refine (hr.continuousOn.div continuousOn_id fun θ hθ => (mem_Ioi.mp hθ).ne').add
    ((Real.continuousOn_log.mono fun θ hθ => (mem_Ioi.mp hθ).ne').mul hr'.continuousOn)

variable {ι : Type} [Fintype ι]

/-- **B0, count form**: `|cutNS| ≤ (6J/c)(Λ°(X) + κ(X)) Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem abs_cutNS_le_count {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω ω₁ : ℝ → ℝ}
    {t₁ X : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hω0 : ∀ θ ∈ Icc 1 t₁, ω θ = 0)
    (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X)) :
    |cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X|
      ≤ 6 * (Fintype.card ι : ℝ) / c * (lamCount ω t₁ X + kapCount ω ω₁ t₁ X)
        * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  have hsd : 4 < 3 * t₁ ^ 2 := by nlinarith
  rw [cutNS_eq_bdry_add_rem a hg hg₁ hg₂c hang (by linarith) hχ0 (fun i => (hχc i).le) (by linarith) hsd
    hω0 hωd hω₁]
  have hB := bdry_le_count a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ht₁ hω0
  have hR := rem_le_count a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ht₁ hωd hω₁
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hB hR
    _ = _ := by ring

/-- **hNS from a floor**: `κ_P Σ aᵢ²∫₁^X ψᵢ² ≤ N` gives `PositionTailFullTail`'s `hNS` with `ε_c = 0`. -/
theorem NS_of_floor {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω ω₁ : ℝ → ℝ}
    {t₁ X κP : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hω0 : ∀ θ ∈ Icc 1 t₁, ω θ = 0)
    (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X))
    (hκ : 0 < κP)
    (hFF : κP * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ 0 * (-(cutW ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + 6 * (Fintype.card ι : ℝ) / c * (lamCount ω t₁ X + kapCount ω ω₁ t₁ X) / κP
          * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  have hb := abs_cutNS_le_count a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ht₁ hω0 hωd hω₁
  have hK : 0 ≤ 6 * (Fintype.card ι : ℝ) / c * (lamCount ω t₁ X + kapCount ω ω₁ t₁ X) :=
    mul_nonneg (div_nonneg (by positivity) (by linarith))
      (add_nonneg (lamCount_nonneg ht₁) (kapCount_nonneg ht₁))
  set K := 6 * (Fintype.card ι : ℝ) / c * (lamCount ω t₁ X + kapCount ω ω₁ t₁ X)
  set P := ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
  set N := ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2
  have hP : P ≤ N / κP := by rw [le_div_iff₀ hκ, mul_comm]; exact hFF
  rw [zero_mul, zero_add]
  calc _ ≤ K * P := (le_abs_self _).trans hb
    _ ≤ K * (N / κP) := mul_le_mul_of_nonneg_left hP hK
    _ = K / κP * N := by ring

/-- The `X`-uniform form, with the tails `Λ°(X) ≤ Λ̄` and `κ(X) ≤ κ̄` as hypotheses. -/
theorem NS_of_floor_unif {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω ω₁ : ℝ → ℝ}
    {t₁ X κP Λbar κbar : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hω0 : ∀ θ ∈ Icc 1 t₁, ω θ = 0)
    (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X))
    (hκ : 0 < κP)
    (hFF : κP * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hΛ : lamCount ω t₁ X ≤ Λbar) (hκbar : kapCount ω ω₁ t₁ X ≤ κbar) :
    cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ 0 * (-(cutW ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + 6 * (Fintype.card ι : ℝ) / c * (Λbar + κbar) / κP
          * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  have h := NS_of_floor a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ht₁ hω0 hωd hω₁ hκ hFF
  have hN : 0 ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hN))
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hΛ hκbar) ?_) hκ.le
  exact div_nonneg (by positivity) (by linarith)

end Cvs.L2a.CutEstimateFrameFloor
