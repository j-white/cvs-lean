import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling integrals `W`, `Δ` and the exact margin `W − 2Δ ≥ g*` on `T ≤ ¾`

`W(T) = ∫_{asin√T}^{π/2} √(sin²φ − T) dφ` and `Δ(T) = ½∫_{asin√T}^{π/3} √(sin²φ − T) dφ`. The difference
`W − 2Δ` is the integral over `[π/3, π/2]`, antitone in `T`, so for `T ≤ ¾` it is at least
`g* = ∫_{π/3}^{π/2} √(sin²φ − ¾) dφ > 0`; also `W ≥ 0`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace Cvs.Prolate.TunnellingIntegralMargin

/-- The tunnelling integrand `√(sin²φ − T)`. -/
def tunF (T φ : ℝ) : ℝ := √(sin φ ^ 2 - T)

theorem continuous_tunF (T : ℝ) : Continuous (tunF T) :=
  ((continuous_sin.pow 2).sub continuous_const).sqrt

theorem intervalIntegrable_tunF (T a b : ℝ) : IntervalIntegrable (tunF T) volume a b :=
  (continuous_tunF T).intervalIntegrable a b

/-- The tunnelling rate `W(T) = ∫_{asin√T}^{π/2} √(sin²φ − T) dφ`. -/
def tunW (T : ℝ) : ℝ := ∫ φ in arcsin √T..π / 2, tunF T φ

/-- The cell-floor exponent `Δ(T) = ½∫_{asin√T}^{π/3} √(sin²φ − T) dφ`. -/
def tunD (T : ℝ) : ℝ := (1 / 2) * ∫ φ in arcsin √T..π / 3, tunF T φ

/-- The margin constant `g* = ∫_{π/3}^{π/2} √(sin²φ − ¾) dφ`. -/
def gStar : ℝ := ∫ φ in π / 3..π / 2, tunF (3 / 4) φ

/-- `W(T) ≥ 0`. -/
theorem tunW_nonneg (T : ℝ) : 0 ≤ tunW T :=
  integral_nonneg (arcsin_le_pi_div_two _) fun _ _ => sqrt_nonneg _

/-- `W(T) − 2Δ(T) = ∫_{π/3}^{π/2} √(sin²φ − T) dφ`. -/
theorem tunW_sub_two_tunD (T : ℝ) :
    tunW T - 2 * tunD T = ∫ φ in π / 3..π / 2, tunF T φ := by
  unfold tunW tunD
  rw [← integral_add_adjacent_intervals (intervalIntegrable_tunF T (arcsin √T) (π / 3))
    (intervalIntegrable_tunF T (π / 3) (π / 2))]
  ring

/-- `g* > 0`. -/
theorem gStar_pos : 0 < gStar := by
  unfold gStar
  refine intervalIntegral_pos_of_pos_on (intervalIntegrable_tunF _ _ _) (fun φ hφ => ?_)
    (by linarith [pi_pos])
  have hs : sin (π / 3) < sin φ :=
    strictMonoOn_sin ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      ⟨by linarith [pi_pos, hφ.1], hφ.2.le⟩ hφ.1
  rw [sin_pi_div_three] at hs
  have h3 : 0 < √3 / 2 := by positivity
  have hsq : 3 / 4 < sin φ ^ 2 := by
    have := mul_lt_mul hs hs.le h3 (by linarith)
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact sqrt_pos.mpr (by linarith)

/-- **The tunnelling margin**: `g* ≤ W(T) − 2Δ(T)` for every `T ≤ ¾`. -/
theorem gStar_le_tunW_sub {T : ℝ} (hT : T ≤ 3 / 4) : gStar ≤ tunW T - 2 * tunD T := by
  rw [tunW_sub_two_tunD T]
  exact integral_mono_on (by linarith [pi_pos]) (intervalIntegrable_tunF _ _ _) (intervalIntegrable_tunF _ _ _)
    fun φ _ => sqrt_le_sqrt (by linarith)

/-- For `κ ≥ ½` and `T ≤ ¾`, `κW(T) − Δ(T) ≥ g*/2`. -/
theorem half_gStar_le {κ T : ℝ} (hκ : 1 / 2 ≤ κ) (hT : T ≤ 3 / 4) : gStar / 2 ≤ κ * tunW T - tunD T := by
  have h1 := gStar_le_tunW_sub hT
  have h2 : 1 / 2 * tunW T ≤ κ * tunW T := mul_le_mul_of_nonneg_right hκ (tunW_nonneg T)
  linarith

end Cvs.Prolate.TunnellingIntegralMargin

end
