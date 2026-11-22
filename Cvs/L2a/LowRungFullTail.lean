import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.PositionTailSquareIntegral
import Cvs.L2a.PositionToFullTailBound
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.EdgeLayerDerivativeMass
import Cvs.Prolate.Envelope.FarRadialDerivative
import Cvs.Prolate.Envelope.FarRadialEnvelope
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.LowRungRadialTailEdge
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full tail of a low prolate rung

For an angular prolate rung with `c ≥ 100` and `0 ≤ χ ≤ (2/5)c²`, `ψ²` is integrable on `(1, ∞)` and
`∫_{θ>1} F_∞² ≤ ∫_{θ>1} ψ² + Kfr(c)·ψ(1)²`, where `F_∞` is the full tail of `ψ` and `Kfr(c)` is the
frame constant at unit edge value.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.LowRungFullTail

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)

/-- The frame constant at unit edge value. -/
def Kfr (c : ℝ) : ℝ :=
  π ^ 2 / 6 * (64 * exp 1 / c)
  + 2 * (π ^ 2 / 6) * Cvs.L2a.PositionTailEdgeRow.rowC c 1 (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)))
      (√(64 * exp 1 / c)) (√(256 / 3 * exp 1 * c)) (9 / 10)
  + 8 * (14 / 3 * (√(64 * exp 1 / c) * √(256 / 3 * exp 1 * c)) / c ^ 2)
  + 16 / 9 * (π ^ 2 / 6) ^ 2 * (64 * exp 1 / c)

/-- The edge-row constant is homogeneous of degree two in its four amplitudes. -/
lemma rowC_smul (c t A A₁ B D κ : ℝ) :
    Cvs.L2a.PositionTailEdgeRow.rowC c (t * A) (t * A₁) (t * B) (t * D) κ
      = t ^ 2 * Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ := by
  unfold Cvs.L2a.PositionTailEdgeRow.rowC; ring

/-- **The full tail of a low rung**: `∫_{θ>1} F_∞² ≤ ∫_{θ>1} ψ² + Kfr(c)·ψ(1)²`. -/
theorem integral_fullTail_rung_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) :
    IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) ∧
    ∫ θ in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (psi c g) θ ^ 2
      ≤ (∫ ξ in Ioi 1, psi c g ξ ^ 2) + Kfr c * psi c g 1 ^ 2 := by
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
  have hψc : Continuous ψ := (Cvs.L2a.FullTailConvergence.contDiff_psi hgc c).continuous
  -- integrability of `ψ²` on `(1, ∞)`
  have hint : IntegrableOn (fun ξ => ψ ξ ^ 2) (Ioi 1) := by
    set f := (Ioi (1 : ℝ)).indicator ψ
    have hf : Measurable f := hψc.measurable.indicator measurableSet_Ioi
    have hb : ∀ θ, 0 < θ → |f θ| ≤ 2 * |ψ 1| / θ := by
      intro θ hθ
      by_cases h : θ ∈ Ioi (1 : ℝ)
      · simp only [f, indicator_of_mem h]
        exact Cvs.Prolate.LowRungRadialTailEdge.abs_psi_le_edge hg hg₁ hg₂c hang hc hχ0 hχ (le_of_lt h)
      · simp only [f, indicator_of_notMem h, abs_zero]; positivity
    have h := Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hf hb
    refine h.congr_fun (fun θ hθ => ?_) measurableSet_Ioi
    simp only [f, indicator_of_mem hθ]
  refine ⟨hint, ?_⟩
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
  -- the constant
  have hconst : π ^ 2 / 6 * (a * b) ^ 2
        + 2 * (π ^ 2 / 6) * Cvs.L2a.PositionTailEdgeRow.rowC c (a * 1) (a * a₁) (a * b) (a * d) (9 / 10)
        + 8 * (14 / 3 * ((a * b) * (a * d)) / c ^ 2) + 16 / 9 * (π ^ 2 / 6) ^ 2 * (a * b) ^ 2
      = Kfr c * ψ 1 ^ 2 := by
    rw [rowC_smul, Kfr, ← hb, ← hd, ← ha₁, ← hb2, ← ha2]; ring
  refine Cvs.L2a.PositionToFullTailBound.integral_fullTail_sq_le hg hg₁ hg₂c hc0 fun X hX => ?_
  have h := Cvs.L2a.PositionTailSquareIntegral.integral_posTail_sq_le hψ hv hvc hode hc0 hχ0 hχc.le (by norm_num)
    (by norm_num) hq hA hA₁ (by positivity) (by positivity) hψB hvD hX
  have hnear : ∫ θ in (1 : ℝ)..X, ψ θ ^ 2 ≤ ∫ ξ in Ioi 1, ψ ξ ^ 2 := by
    rw [intervalIntegral.integral_of_le hX]
    exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (Filter.Eventually.of_forall fun θ hθ => Ioc_subset_Ioi_self hθ)
  linarith
end Cvs.L2a.LowRungFullTail
