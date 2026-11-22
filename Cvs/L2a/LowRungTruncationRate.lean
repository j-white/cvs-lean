import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.LowRungFullTail
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.PositionTailTruncationGap
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.EdgeLayerDerivativeMass
import Cvs.Prolate.Envelope.FarRadialDerivative
import Cvs.Prolate.Envelope.FarRadialEnvelope
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.LowRungRadialMassBeyond
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncation rate of a low prolate rung against its full tail

For an angular prolate rung with `c ≥ 100` and `0 ≤ χ ≤ (2/5)c²`, for every `k > 1`,
`∫_{θ>1} (posTail ψ k − F_∞)² ≤ Krate(c)·ψ(1)²·k^{-1/2}`, where `F_∞` is the full tail of `ψ`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.L2a.LowRungTruncationRate

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail)

/-- The truncation-rate constant at unit edge value. -/
def Krate (c : ℝ) : ℝ :=
  1800 * (400 * exp 1 / c
    + Cvs.L2a.PositionTailEdgeRow.rowC c 1 (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)))
      (√(64 * exp 1 / c)) (√(256 / 3 * exp 1 * c)) (9 / 10)
    + 64 * exp 1 / c + √(64 * exp 1 / c) * √(256 / 3 * exp 1 * c) / c ^ 2)

/-- **The truncation rate against the full tail**: `∫_{θ>1} (posTail ψ k − F_∞)² ≤ Krate(c)·ψ(1)²·k^{-1/2}`. -/
theorem integral_posTail_sub_fullTail_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {k : ℝ} (hk : 1 < k) :
    ∫ θ in Ioi 1, (posTail (psi c g) k θ - fullTail (psi c g) θ) ^ 2
      ≤ Krate c * psi c g 1 ^ 2 * k ^ (-(1 / 2) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s))) with hvdef
  set v' := kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) with hv'def
  set ψ := psi c g with hψdef
  have hvc : Continuous v' := by
    refine continuous_iff_continuousAt.2 fun ξ => ?_
    refine (Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (k' := fun ξ s => c ^ 3 * s ^ 3 * sin (c * ξ * s))
      (C := |c| ^ 3) hgc (fun s => by fun_prop) (fun ξ => by fun_prop) (fun ξ => by fun_prop) ?_ ?_ ξ).continuousAt
    · intro ξ s
      have := ((((hasDerivAt_id ξ).const_mul c |>.mul_const s).cos).const_mul (c ^ 2 * s ^ 2)).neg
      refine this.congr_deriv ?_; simp; ring
    · intro ξ s hs
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      calc |c| ^ 3 * |s| ^ 3 * |sin (c * ξ * s)| ≤ |c| ^ 3 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg s) hs) (by positivity))
              (abs_sin_le_one _) (abs_nonneg _) (by positivity)
        _ = |c| ^ 3 := by ring
  -- the envelope constants
  set a := |ψ 1| with ha
  set a₁ := 4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)) with ha₁
  set b := √(64 * exp 1 / c) with hb
  set d := √(256 / 3 * exp 1 * c) with hd
  have hb2 : b ^ 2 = 64 * exp 1 / c := Real.sq_sqrt (by positivity)
  have hd2 : d ^ 2 = 256 / 3 * exp 1 * c := Real.sq_sqrt (by positivity)
  have ha2 : a ^ 2 = ψ 1 ^ 2 := sq_abs _
  have hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ a * 1 := fun θ hθ => by
    have hs : ψ θ ^ 2 ≤ ψ 1 ^ 2 :=
      Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := 2) hχc hθ (fun r _ => hψ r) (fun r _ => hv r)
        (fun r _ => hode r)
    rw [mul_one]; simpa using sq_le_sq.mp hs
  have hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ a * a₁ := by
    have h := Cvs.Prolate.EdgeLayerDerivativeMass.integral_abs_deriv_le hg hg₁ hg₂c hang hc hχ0 hχ
    calc _ ≤ _ := h
      _ = a * a₁ := by rw [ha, ha₁]; ring
  have hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ a * b / ξ := fun ξ hξ => by
    have hξ0 : 0 < ξ := by linarith
    have h := Cvs.Prolate.Envelope.FarRadialEnvelope.sq_psi_far_le hg hg₁ hg₂c hang hc hχ0 hχ hξ
    have h' : ψ ξ ^ 2 ≤ (a * b / ξ) ^ 2 := by
      calc ψ ξ ^ 2 ≤ 64 * exp 1 * ψ 1 ^ 2 / (c * ξ ^ 2) := h
        _ = (a * b / ξ) ^ 2 := by rw [div_pow, mul_pow, hb2, ha2]; field_simp
    have := Real.abs_le_sqrt h'
    rwa [Real.sqrt_sq (by positivity)] at this
  have hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ a * d / ξ := fun ξ hξ => by
    have hξ0 : 0 < ξ := by linarith
    have h := Cvs.Prolate.Envelope.FarRadialDerivative.sq_deriv_far_le hg hg₁ hg₂c hang hc hχ0 hχ hξ
    have h' : v ξ ^ 2 ≤ (a * d / ξ) ^ 2 := by
      calc v ξ ^ 2 ≤ 256 / 3 * exp 1 * c * ψ 1 ^ 2 / ξ ^ 2 := h
        _ = (a * d / ξ) ^ 2 := by rw [div_pow, mul_pow, hd2, ha2]; ring
    have := Real.abs_le_sqrt h'
    rwa [Real.sqrt_sq (by positivity)] at this
  have hq : ∀ ξ, 2 ≤ ξ → 9 / 10 * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ := fun ξ hξ => by
    have : 4 ≤ ξ ^ 2 := by nlinarith
    nlinarith
  have hT : ∀ b₀ b', 1 ≤ b₀ → b₀ ≤ b' → ∫ θ in b₀..b', ψ θ ^ 2 ≤ 400 * exp 1 * ψ 1 ^ 2 / c / b₀ :=
    fun b₀ b' h1 h2 => by
      have := Cvs.Prolate.LowRungRadialMassBeyond.integral_sq_le hg hg₁ hg₂c hang hc hχ0 hχ h1 h2
      rwa [div_div]
  -- the gap bound, uniform in `X`
  set G := Krate c / 1800 * ψ 1 ^ 2 * (18 * (2 + Real.log k) ^ 2 / k) with hG
  have hgap : ∀ X, k ≤ X → ∫ θ in Ioi 1, (posTail ψ X θ - posTail ψ k θ) ^ 2 ≤ G := fun X hX => by
    have h := Cvs.L2a.PositionTailTruncationGap.integral_posTail_gap_le_log hψ hv hvc hode hc0 hχ0 hχc.le (by norm_num)
      (by norm_num) hq hA hA₁ (by positivity) (by positivity) hψB hvD hT hk.le hX
    refine h.trans (le_of_eq ?_)
    rw [hG, Krate, Cvs.L2a.LowRungFullTail.rowC_smul, ← hb, ← hd, ← ha₁]
    have : a * b * (a * d) = a ^ 2 * (b * d) := by ring
    rw [this, mul_pow, ha2, hb2]
    field_simp
  -- pass `X → ∞`
  set F := fullTail ψ
  set Kb := Cvs.L2a.FullTailConvergence.K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hKb
  set BG := Cvs.L2a.FullTailConvergence.BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hτ := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc0
  have hDk : IntegrableOn (fun θ => (posTail ψ k θ - F θ) ^ 2) (Ioi 1) :=
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c k).sub hτ)
      fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc0 k hθ
  have key : ∀ ε : ℝ, 0 < ε → ∀ X : ℝ, k ≤ X →
      ∫ θ in Ioi 1, (posTail ψ k θ - F θ) ^ 2 ≤ (1 + ε) * G + (1 + 1 / ε) * (Kb / √X) := fun ε hε X hX => by
    have hX1 : 1 ≤ X := by linarith
    have hDX : IntegrableOn (fun θ => (posTail ψ X θ - F θ) ^ 2) (Ioi 1) :=
      Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c X).sub hτ)
        fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc0 X hθ
    have hgX : IntegrableOn (fun θ => (posTail ψ X θ - posTail ψ k θ) ^ 2) (Ioi 1) := by
      refine Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (K := 4 * BG)
        ((Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c X).sub
          (Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c k)) fun θ hθ => ?_
      have h1 := Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc0 X hθ
      have h2 := Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc0 k hθ
      have e : posTail ψ X θ - posTail ψ k θ = (posTail ψ X θ - F θ) - (posTail ψ k θ - F θ) := by ring
      rw [e]
      calc _ ≤ |posTail ψ X θ - F θ| + |posTail ψ k θ - F θ| := abs_sub _ _
        _ ≤ 2 * BG / θ + 2 * BG / θ := add_le_add h1 h2
        _ = 4 * BG / θ := by ring
    have hrate := (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc0 hX1).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc0 _ _ hX1)
    have hpt : ∀ θ ∈ Ioi (1 : ℝ), (posTail ψ k θ - F θ) ^ 2
        ≤ (1 + ε) * (posTail ψ X θ - posTail ψ k θ) ^ 2 + (1 + 1 / ε) * (posTail ψ X θ - F θ) ^ 2 :=
      fun θ _ => by
      have h : 0 ≤ (ε * (posTail ψ X θ - posTail ψ k θ) + (posTail ψ X θ - F θ)) ^ 2 / ε := by positivity
      have e : (1 + ε) * (posTail ψ X θ - posTail ψ k θ) ^ 2 + (1 + 1 / ε) * (posTail ψ X θ - F θ) ^ 2
            - (posTail ψ k θ - F θ) ^ 2
          = (ε * (posTail ψ X θ - posTail ψ k θ) + (posTail ψ X θ - F θ)) ^ 2 / ε := by
        field_simp; ring
      linarith
    have hint := setIntegral_mono_on hDk ((hgX.const_mul (1 + ε)).add (hDX.const_mul (1 + 1 / ε)))
      measurableSet_Ioi hpt
    simp only [Pi.add_apply] at hint
    rw [integral_add (hgX.const_mul _) (hDX.const_mul _), integral_const_mul, integral_const_mul] at hint
    have h1 := mul_le_mul_of_nonneg_left (hgap X hX) (by linarith : (0 : ℝ) ≤ 1 + ε)
    have h2 := mul_le_mul_of_nonneg_left hrate (by positivity : (0 : ℝ) ≤ 1 + 1 / ε)
    linarith
  have hlimX : ∀ ε : ℝ, 0 < ε → ∫ θ in Ioi 1, (posTail ψ k θ - F θ) ^ 2 ≤ (1 + ε) * G := fun ε hε => by
    have ht : Tendsto (fun X : ℝ => (1 + ε) * G + (1 + 1 / ε) * (Kb / √X)) atTop (nhds ((1 + ε) * G)) := by
      have h0 : Tendsto (fun X : ℝ => Kb / √X) atTop (nhds 0) :=
        (tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop))
      simpa using tendsto_const_nhds.add (h0.const_mul (1 + 1 / ε))
    exact ge_of_tendsto ht (eventually_atTop.2 ⟨k, fun X hX => key ε hε X hX⟩)
  have hlimε : Tendsto (fun ε : ℝ => (1 + ε) * G) (nhdsWithin 0 (Ioi 0)) (nhds G) := by
    have : Tendsto (fun ε : ℝ => (1 + ε) * G) (nhds 0) (nhds ((1 + 0) * G)) :=
      ((tendsto_const_nhds.add tendsto_id).mul tendsto_const_nhds)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hmain : ∫ θ in Ioi 1, (posTail ψ k θ - F θ) ^ 2 ≤ G :=
    ge_of_tendsto hlimε (eventually_nhdsWithin_of_forall fun ε hε => hlimX ε hε)
  -- `(2 + log k)²/k ≤ 100 k^{-1/2}`
  have hk0 : 0 < k := by linarith
  have hlog := Cvs.L2a.L1FullTailWinfBound.one_add_log_sq_le hk.le
  have hl0 := Real.log_nonneg hk.le
  have hL : 18 * (2 + Real.log k) ^ 2 / k ≤ 1800 * k ^ (-(1 / 2) : ℝ) := by
    have h4 : (2 + Real.log k) ^ 2 ≤ 4 * (1 + Real.log k) ^ 2 := by nlinarith
    have hk' : k ^ (1 / 2 : ℝ) / k = k ^ (-(1 / 2) : ℝ) := by
      rw [div_eq_iff hk0.ne']
      calc k ^ (1 / 2 : ℝ) = k ^ (-(1 / 2) + 1 : ℝ) := by norm_num
        _ = k ^ (-(1 / 2) : ℝ) * k := by rw [rpow_add hk0, rpow_one]
    calc 18 * (2 + Real.log k) ^ 2 / k ≤ 18 * (4 * (25 * k ^ (1 / 2 : ℝ))) / k := by
          apply div_le_div_of_nonneg_right _ hk0.le; nlinarith
      _ = 1800 * (k ^ (1 / 2 : ℝ) / k) := by ring
      _ = 1800 * k ^ (-(1 / 2) : ℝ) := by rw [hk']
  have hK0 : 0 ≤ Krate c := by
    unfold Krate Cvs.L2a.PositionTailEdgeRow.rowC; positivity
  calc _ ≤ G := hmain
    _ ≤ Krate c / 1800 * ψ 1 ^ 2 * (1800 * k ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = Krate c * psi c g 1 ^ 2 * k ^ (-(1 / 2) : ℝ) := by ring

end Cvs.L2a.LowRungTruncationRate
