import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Upstream.FirstDerivativeTestVariation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form of the second-derivative test, in variation form

With a window `[c₁, c₂]` of width at most `2δ` outside of which `|φ'| ≥ λδ`, and `|g| ≤ A`, `∫|g'| ≤ V`,
`∫|φ''| ≤ W` on `[a, b]`, the integral `|∫_a^b g cos φ|` is at most `2δA + 2(2A + V)/(λδ) + 2AW/(λδ)²`: the
window contributes its width, each outer piece the variation-form first-derivative test of Cvs.Upstream.FirstDerivativeTestVariation, so no
monotonicity of the phase derivative is used anywhere.
-/

namespace Cvs.Upstream.SecondDerivativeWindowTest

open Real Set MeasureTheory intervalIntegral
open Cvs.Upstream.FirstDerivativeTestVariation

/-- **The window test in variation form**: `|∫_a^b g cos φ| ≤ 2δA + 2(2A + V)/(λδ) + 2AW/(λδ)²`. -/
theorem window_test_var {a c₁ c₂ b lam δ A V W : ℝ} {g g₁ φ φ₁ φ₂ : ℝ → ℝ}
    (hac : a ≤ c₁) (hcc : c₁ ≤ c₂) (hcb : c₂ ≤ b) (hlam : 0 < lam) (hδ : 0 < δ) (hwidth : c₂ - c₁ ≤ 2 * δ)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g₁ t) t) (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t ∈ Icc a b, HasDerivAt φ₁ (φ₂ t) t)
    (hleft : ∀ t ∈ Icc a c₁, φ₁ t ≤ -(lam * δ)) (hright : ∀ t ∈ Icc c₂ b, lam * δ ≤ φ₁ t)
    (hc₂ : ContinuousOn φ₂ (Icc a b)) (hc₁ : ContinuousOn g₁ (Icc a b))
    (hA : ∀ t ∈ Icc a b, |g t| ≤ A) (hV : ∫ t in a..b, |g₁ t| ≤ V) (hW : ∫ t in a..b, |φ₂ t| ≤ W) :
    |∫ t in a..b, g t * Real.cos (φ t)|
      ≤ 2 * δ * A + 2 * ((2 * A + V) / (lam * δ)) + 2 * (A * W / (lam * δ) ^ 2) := by
  have hab : a ≤ b := hac.trans (hcc.trans hcb)
  have hμ : 0 < lam * δ := mul_pos hlam hδ
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA a ⟨le_rfl, hab⟩)
  have hsub1 : Icc a c₁ ⊆ Icc a b := Icc_subset_Icc le_rfl (hcc.trans hcb)
  have hsub2 : Icc c₁ c₂ ⊆ Icc a b := Icc_subset_Icc hac hcb
  have hsub3 : Icc c₂ b ⊆ Icc a b := Icc_subset_Icc (hac.trans hcc) le_rfl
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun t => g t * Real.cos (φ t)) (Icc a b) :=
    hgc.mul (Real.continuous_cos.comp_continuousOn hφc)
  have hI1 : IntervalIntegrable (fun t => g t * Real.cos (φ t)) volume a c₁ :=
    (hfc.mono hsub1).intervalIntegrable_of_Icc hac
  have hI2 : IntervalIntegrable (fun t => g t * Real.cos (φ t)) volume c₁ c₂ :=
    (hfc.mono hsub2).intervalIntegrable_of_Icc hcc
  have hI3 : IntervalIntegrable (fun t => g t * Real.cos (φ t)) volume c₂ b :=
    (hfc.mono hsub3).intervalIntegrable_of_Icc hcb
  -- the integrals of `|g'|` and `|φ''|` over a piece are at most `V` and `W`
  have hg₁abs : ContinuousOn (fun t => |g₁ t|) (Icc a b) := hc₁.abs
  have hφ₂abs : ContinuousOn (fun t => |φ₂ t|) (Icc a b) := hc₂.abs
  have hVpiece : ∀ p q, a ≤ p → p ≤ q → q ≤ b → ∫ t in p..q, |g₁ t| ≤ V := fun p q hap hpq hqb =>
    (integral_mono_interval hap hpq hqb (Filter.Eventually.of_forall fun t => abs_nonneg _)
      (hg₁abs.intervalIntegrable_of_Icc hab)).trans hV
  have hWpiece : ∀ p q, a ≤ p → p ≤ q → q ≤ b → ∫ t in p..q, |φ₂ t| ≤ W := fun p q hap hpq hqb =>
    (integral_mono_interval hap hpq hqb (Filter.Eventually.of_forall fun t => abs_nonneg _)
      (hφ₂abs.intervalIntegrable_of_Icc hab)).trans hW
  -- the left piece
  have hL := piece_le_var (μ := lam * δ) hac hμ (fun t ht => hg t (hsub1 ht)) (fun t ht => hφ t (hsub1 ht))
    (fun t ht => hφ₁ t (hsub1 ht)) (Or.inr hleft) (hc₂.mono hsub1) (hc₁.mono hsub1)
    (fun t ht => hA t (hsub1 ht)) (hVpiece a c₁ le_rfl hac (hcc.trans hcb)) (hWpiece a c₁ le_rfl hac (hcc.trans hcb))
  -- the right piece
  have hR := piece_le_var (μ := lam * δ) hcb hμ (fun t ht => hg t (hsub3 ht)) (fun t ht => hφ t (hsub3 ht))
    (fun t ht => hφ₁ t (hsub3 ht)) (Or.inl hright) (hc₂.mono hsub3) (hc₁.mono hsub3)
    (fun t ht => hA t (hsub3 ht)) (hVpiece c₂ b (hac.trans hcc) hcb le_rfl) (hWpiece c₂ b (hac.trans hcc) hcb le_rfl)
  -- the window
  have hWin : |∫ t in c₁..c₂, g t * Real.cos (φ t)| ≤ (c₂ - c₁) * A := by
    have hpt : ∀ t ∈ Ioc c₁ c₂, ‖g t * Real.cos (φ t)‖ ≤ A := fun t ht => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |g t| * |Real.cos (φ t)| ≤ A * 1 :=
            mul_le_mul (hA t (hsub2 ⟨ht.1.le, ht.2⟩)) (Real.abs_cos_le_one _) (abs_nonneg _) hA0
        _ = A := mul_one _
    have key := norm_integral_le_of_norm_le hcc (Filter.Eventually.of_forall hpt)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => A) volume c₁ c₂)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul] at key
    exact key
  rw [← integral_add_adjacent_intervals (hI1.trans hI2) hI3, ← integral_add_adjacent_intervals hI1 hI2]
  have hWin' : |∫ t in c₁..c₂, g t * Real.cos (φ t)| ≤ 2 * δ * A := by
    have := mul_le_mul_of_nonneg_right hwidth hA0
    linarith
  calc |(∫ t in a..c₁, g t * Real.cos (φ t)) + (∫ t in c₁..c₂, g t * Real.cos (φ t))
        + ∫ t in c₂..b, g t * Real.cos (φ t)|
      ≤ |∫ t in a..c₁, g t * Real.cos (φ t)| + |∫ t in c₁..c₂, g t * Real.cos (φ t)|
        + |∫ t in c₂..b, g t * Real.cos (φ t)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((2 * A + V) / (lam * δ) + A * W / (lam * δ) ^ 2) + 2 * δ * A
        + ((2 * A + V) / (lam * δ) + A * W / (lam * δ) ^ 2) :=
        add_le_add (add_le_add hL hWin') hR
    _ = 2 * δ * A + 2 * ((2 * A + V) / (lam * δ)) + 2 * (A * W / (lam * δ) ^ 2) := by ring

end Cvs.Upstream.SecondDerivativeWindowTest
