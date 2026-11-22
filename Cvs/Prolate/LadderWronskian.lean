import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ladder Wronskian

For angular solutions `g_a`, `g_b` at levels `χ_a`, `χ_b`, `(1 − s²)(g_b′g_a − g_b g_a′) = (χ_b − χ_a)∫_s^1 g_a g_b`.
Where both are positive on `[s*, 1]`, `(log(g_b/g_a))′` is that over `(1 − s²)g_a g_b`, so the endpoint ratio is
the ratio at `s*` times `exp((χ_b − χ_a)∫_{s*}^1 (1/((1 − s²)g_a g_b))∫_s^1 g_a g_b)`, nondecreasing in `s*` reversed.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.LadderWronskian

/-- **The ladder Wronskian**: `(1 − s²)(g_b′g_a − g_b g_a′)(s) = (χ_b − χ_a)∫_s^1 g_a g_b` on `[−1, 1]`. -/
theorem wronskian_eq {ga ga₁ ga₂ gb gb₁ gb₂ : ℝ → ℝ} {c χa χb s : ℝ}
    (ha : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga (ga₁ t) t) (ha₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga₁ (ga₂ t) t)
    (hanga : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * ga₂ t - 2 * t * ga₁ t - c ^ 2 * t ^ 2 * ga t + χa * ga t = 0)
    (hb : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb (gb₁ t) t) (hb₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb₁ (gb₂ t) t)
    (hangb : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * gb₂ t - 2 * t * gb₁ t - c ^ 2 * t ^ 2 * gb t + χb * gb t = 0)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    (1 - s ^ 2) * (gb₁ s * ga s - gb s * ga₁ s) = (χb - χa) * ∫ t in s..1, ga t * gb t := by
  set F : ℝ → ℝ := fun t => (1 - t ^ 2) * (gb₁ t * ga t - gb t * ga₁ t) with hF
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hsub : uIcc s 1 ⊆ uIcc (-1 : ℝ) 1 := by
    rw [hI, uIcc_of_le hs.2]; exact Icc_subset_Icc_left hs.1
  have hd : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt F (-(χb - χa) * (ga t * gb t)) t := by
    intro t ht
    have hp : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have hw : HasDerivAt (fun t => gb₁ t * ga t - gb t * ga₁ t)
        (gb₂ t * ga t + gb₁ t * ga₁ t - (gb₁ t * ga₁ t + gb t * ga₂ t)) t :=
      ((hb₁ t ht).mul (ha t ht)).sub ((hb t ht).mul (ha₁ t ht))
    have this : HasDerivAt F (-(2 * t) * (gb₁ t * ga t - gb t * ga₁ t)
        + (1 - t ^ 2) * (gb₂ t * ga t + gb₁ t * ga₁ t - (gb₁ t * ga₁ t + gb t * ga₂ t))) t := hp.mul hw
    refine this.congr_deriv ?_
    have e1 := hanga t ht
    have e2 := hangb t ht
    linear_combination ga t * e2 - gb t * e1
  have hgc : ContinuousOn (fun t => ga t * gb t) (uIcc (-1 : ℝ) 1) := fun t ht =>
    ((ha t ht).continuousAt.mul (hb t ht).continuousAt).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (a := s) (b := 1)
    (fun t ht => hd t (hsub ht)) ((hgc.mono hsub).const_smul (-(χb - χa))).intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hint
  have hF1 : F 1 = 0 := by simp [F]
  rw [hF1] at hint
  simp only [F] at hint
  linarith

/-- **The ladder log-derivative**: where `g_a g_b ≠ 0` and `s² < 1`,
`g_b′/g_b − g_a′/g_a = (χ_b − χ_a)(∫_s^1 g_a g_b)/((1 − s²) g_a g_b)`. -/
theorem logderiv_sub_eq {ga ga₁ ga₂ gb gb₁ gb₂ : ℝ → ℝ} {c χa χb s : ℝ}
    (ha : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga (ga₁ t) t) (ha₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga₁ (ga₂ t) t)
    (hanga : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * ga₂ t - 2 * t * ga₁ t - c ^ 2 * t ^ 2 * ga t + χa * ga t = 0)
    (hb : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb (gb₁ t) t) (hb₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb₁ (gb₂ t) t)
    (hangb : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * gb₂ t - 2 * t * gb₁ t - c ^ 2 * t ^ 2 * gb t + χb * gb t = 0)
    (hs : s ∈ Icc (-1 : ℝ) 1) (hs1 : s ^ 2 < 1) (hga : ga s ≠ 0) (hgb : gb s ≠ 0) :
    gb₁ s / gb s - ga₁ s / ga s = (χb - χa) * (∫ t in s..1, ga t * gb t) / ((1 - s ^ 2) * (ga s * gb s)) := by
  have hW := wronskian_eq ha ha₁ hanga hb hb₁ hangb hs
  have hp : 1 - s ^ 2 ≠ 0 := by linarith
  rw [← hW]
  field_simp

end Cvs.Prolate.LadderWronskian
