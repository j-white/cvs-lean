import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first-derivative test in variation form

On a piece where the phase derivative keeps one sign and `|φ'| ≥ μ`, with `|g| ≤ A`, `∫|g'| ≤ V` and `∫|φ''| ≤ W`,
`|∫ g cos φ| ≤ (2A + V)/μ + A W/μ²`: no monotonicity of the phase derivative is needed, so the test applies to
the exact Prüfer rates of the rungs, whose oscillating corrections spoil the sign of `φ''` but not its size.
-/

namespace Cvs.Upstream.FirstDerivativeTestVariation

open Real Set MeasureTheory intervalIntegral

/-- **The first-derivative test in variation form**: `|φ'| ≥ μ` of one sign, `|g| ≤ A`, `∫|g'| ≤ V`, `∫|φ''| ≤ W`
give `|∫_p^q g cos φ| ≤ (2A + V)/μ + A W/μ²`. -/
theorem piece_le_var {p q μ A V W : ℝ} {g g₁ φ φ₁ φ₂ : ℝ → ℝ} (hpq : p ≤ q) (hμ : 0 < μ)
    (hg : ∀ t ∈ Icc p q, HasDerivAt g (g₁ t) t) (hφ : ∀ t ∈ Icc p q, HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t ∈ Icc p q, HasDerivAt φ₁ (φ₂ t) t)
    (hsign : (∀ t ∈ Icc p q, μ ≤ φ₁ t) ∨ (∀ t ∈ Icc p q, φ₁ t ≤ -μ))
    (hc₂ : ContinuousOn φ₂ (Icc p q)) (hc₁ : ContinuousOn g₁ (Icc p q))
    (hA : ∀ t ∈ Icc p q, |g t| ≤ A) (hV : ∫ t in p..q, |g₁ t| ≤ V) (hW : ∫ t in p..q, |φ₂ t| ≤ W) :
    |∫ t in p..q, g t * Real.cos (φ t)| ≤ (2 * A + V) / μ + A * W / μ ^ 2 := by
  have hne : ∀ t ∈ Icc p q, φ₁ t ≠ 0 := fun t ht => by
    rcases hsign with h | h
    · exact (lt_of_lt_of_le hμ (h t ht)).ne'
    · exact (lt_of_le_of_lt (h t ht) (by linarith)).ne
  have habs : ∀ t ∈ Icc p q, μ ≤ |φ₁ t| := fun t ht => by
    rcases hsign with h | h
    · rw [abs_of_pos (lt_of_lt_of_le hμ (h t ht))]; exact h t ht
    · rw [abs_of_neg (lt_of_le_of_lt (h t ht) (by linarith))]; linarith [h t ht]
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA p ⟨le_rfl, hpq⟩)
  have huI : uIcc p q = Icc p q := uIcc_of_le hpq
  have hgc : ContinuousOn g (Icc p q) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Icc p q) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hφ₁c : ContinuousOn φ₁ (Icc p q) := fun t ht => (hφ₁ t ht).continuousAt.continuousWithinAt
  -- integration by parts with `u = g/φ₁`, `v = sin φ`
  set u : ℝ → ℝ := fun t => g t / φ₁ t with hu
  set u' : ℝ → ℝ := fun t => (g₁ t * φ₁ t - g t * φ₂ t) / φ₁ t ^ 2 with hu'
  have hud : ∀ t ∈ Icc p q, HasDerivAt u (u' t) t := fun t ht =>
    (hg t ht).div (hφ₁ t ht) (hne t ht)
  have hvd : ∀ t ∈ Icc p q, HasDerivAt (fun t => Real.sin (φ t)) (Real.cos (φ t) * φ₁ t) t := fun t ht =>
    (Real.hasDerivAt_sin _).comp t (hφ t ht)
  have hu'c : ContinuousOn u' (Icc p q) :=
    ((hc₁.mul hφ₁c).sub (hgc.mul hc₂)).div (hφ₁c.pow 2) (fun t ht => pow_ne_zero 2 (hne t ht))
  have hv'c : ContinuousOn (fun t => Real.cos (φ t) * φ₁ t) (Icc p q) :=
    (Real.continuous_cos.comp_continuousOn hφc).mul hφ₁c
  have e : ∫ t in p..q, g t * Real.cos (φ t) = ∫ t in p..q, u t * (Real.cos (φ t) * φ₁ t) := by
    apply integral_congr
    intro t ht
    rw [huI] at ht
    simp only [hu]
    field_simp [hne t ht]
  rw [e, integral_mul_deriv_eq_deriv_mul (fun t ht => hud t (huI ▸ ht)) (fun t ht => hvd t (huI ▸ ht))
    (hu'c.intervalIntegrable_of_Icc hpq) (hv'c.intervalIntegrable_of_Icc hpq)]
  -- the boundary terms
  have hbd : ∀ t ∈ Icc p q, |u t * Real.sin (φ t)| ≤ A / μ := fun t ht => by
    rw [abs_mul, hu]
    simp only
    rw [abs_div]
    calc |g t| / |φ₁ t| * |Real.sin (φ t)| ≤ A / μ * 1 := by
          apply mul_le_mul _ (Real.abs_sin_le_one _) (abs_nonneg _) (div_nonneg hA0 hμ.le)
          exact div_le_div₀ hA0 (hA t ht) hμ (habs t ht)
      _ = A / μ := mul_one _
  -- the integral of `u'` against `sin φ`: `|u'| ≤ |g₁|/μ + A |φ₂|/μ²`
  have hint : |∫ t in p..q, u' t * Real.sin (φ t)| ≤ V / μ + A * W / μ ^ 2 := by
    have hμ2 : 0 < μ ^ 2 := by positivity
    have hpt : ∀ t ∈ Ioc p q, ‖u' t * Real.sin (φ t)‖ ≤ |g₁ t| / μ + A * (|φ₂ t| / μ ^ 2) := fun t ht => by
      have ht' : t ∈ Icc p q := ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |u' t| * |Real.sin (φ t)| ≤ |u' t| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |u' t| := mul_one _
        _ ≤ |g₁ t| / μ + A * (|φ₂ t| / μ ^ 2) := by
            simp only [hu']
            have hφ₁ne := hne t ht'
            have hsq : 0 < φ₁ t ^ 2 := by positivity
            have e1 : (g₁ t * φ₁ t - g t * φ₂ t) / φ₁ t ^ 2 = g₁ t / φ₁ t - g t * (φ₂ t / φ₁ t ^ 2) := by
              field_simp
            rw [e1]
            refine (abs_sub _ _).trans (add_le_add ?_ ?_)
            · rw [abs_div]
              exact div_le_div_of_nonneg_left (abs_nonneg _) hμ (habs t ht')
            · rw [abs_mul, abs_div, abs_pow]
              refine mul_le_mul (hA t ht') ?_ (by positivity) hA0
              have hsq' : μ ^ 2 ≤ |φ₁ t| ^ 2 := by
                have := habs t ht'
                nlinarith [abs_nonneg (φ₁ t)]
              exact div_le_div_of_nonneg_left (abs_nonneg _) hμ2 hsq'
    have hg₁abs : ContinuousOn (fun t => |g₁ t|) (Icc p q) := hc₁.abs
    have hφ₂abs : ContinuousOn (fun t => |φ₂ t|) (Icc p q) := hc₂.abs
    have hbound : IntervalIntegrable (fun t => |g₁ t| / μ + A * (|φ₂ t| / μ ^ 2)) volume p q :=
      ((hg₁abs.div_const μ).add (continuousOn_const.mul (hφ₂abs.div_const _))).intervalIntegrable_of_Icc hpq
    have key := norm_integral_le_of_norm_le hpq (Filter.Eventually.of_forall hpt) hbound
    rw [Real.norm_eq_abs] at key
    have hsplit : ∫ t in p..q, (|g₁ t| / μ + A * (|φ₂ t| / μ ^ 2))
        = (∫ t in p..q, |g₁ t| / μ) + ∫ t in p..q, A * (|φ₂ t| / μ ^ 2) :=
      integral_add ((hg₁abs.div_const μ).intervalIntegrable_of_Icc hpq)
        ((continuousOn_const.mul (hφ₂abs.div_const _)).intervalIntegrable_of_Icc hpq)
    rw [hsplit, intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_div] at key
    calc |∫ t in p..q, u' t * Real.sin (φ t)|
        ≤ (∫ t in p..q, |g₁ t|) / μ + A * ((∫ t in p..q, |φ₂ t|) / μ ^ 2) := key
      _ ≤ V / μ + A * (W / μ ^ 2) :=
          add_le_add (div_le_div_of_nonneg_right hV hμ.le)
            (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hW hμ2.le) hA0)
      _ = V / μ + A * W / μ ^ 2 := by ring
  calc |u q * Real.sin (φ q) - u p * Real.sin (φ p) - ∫ t in p..q, u' t * Real.sin (φ t)|
      ≤ |u q * Real.sin (φ q)| + |u p * Real.sin (φ p)| + |∫ t in p..q, u' t * Real.sin (φ t)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ A / μ + A / μ + (V / μ + A * W / μ ^ 2) :=
        add_le_add (add_le_add (hbd q ⟨hpq, le_rfl⟩) (hbd p ⟨le_rfl, hpq⟩)) hint
    _ = (2 * A + V) / μ + A * W / μ ^ 2 := by ring

end Cvs.Upstream.FirstDerivativeTestVariation
