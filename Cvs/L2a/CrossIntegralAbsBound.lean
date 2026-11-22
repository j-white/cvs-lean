import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Upstream.SturmCrossIdentitySources

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cross integral in absolute value, and the weighted product bound

From the cross identity with sources (Cvs.Upstream.SturmCrossIdentitySources), `|∫ σ f₁f₂|` is at most the boundary term, the two `fu` terms and
the source term in absolute value. Each product integral `∫ FH` against a weight `w > 0` obeys
`|∫ FH| ≤ (λ/2) ∫ F²/w + (1/(2λ)) ∫ wH²` for every `λ > 0`, from `2|FH| ≤ λF²/w + wH²/λ` pointwise; this is
how the `fu` terms become weighted norms of the combination and of its derivative.
-/

namespace Cvs.L2a.CrossIntegralAbsBound

open intervalIntegral Real Set

variable {f₁ u₁ p₁ q₁ r₁ f₂ u₂ p₂ q₂ r₂ : ℝ → ℝ}

/-- **The cross integral in absolute value.** Under the hypotheses of `Cvs.Upstream.SturmCrossIdentitySources.integral_cross_src`,
`|∫ σ f₁f₂| ≤ |boundary| + |∫ α f₁u₂| + |∫ β u₁f₂| + |∫ (σ/D)(p₁f₁r₂ − p₂r₁f₂)|`. -/
theorem abs_integral_cross_le {σ α β : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hp₁ : ∀ r ∈ Icc s t, p₁ r ≠ 0) (hp₂ : ∀ r ∈ Icc s t, p₂ r ≠ 0)
    (hD : ∀ r ∈ Icc s t, p₂ r * q₁ r - p₁ r * q₂ r ≠ 0)
    (hf₁ : ∀ r ∈ Icc s t, HasDerivAt f₁ (u₁ r / p₁ r) r)
    (hu₁ : ∀ r ∈ Icc s t, HasDerivAt u₁ (-(q₁ r * f₁ r) + r₁ r) r)
    (hf₂ : ∀ r ∈ Icc s t, HasDerivAt f₂ (u₂ r / p₂ r) r)
    (hu₂ : ∀ r ∈ Icc s t, HasDerivAt u₂ (-(q₂ r * f₂ r) + r₂ r) r)
    (hA : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (α r) r)
    (hB : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (β r) r)
    (hαc : ContinuousOn α (Icc s t)) (hβc : ContinuousOn β (Icc s t)) (hσc : ContinuousOn σ (Icc s t))
    (hq₁ : ContinuousOn q₁ (Icc s t)) (hq₂ : ContinuousOn q₂ (Icc s t))
    (hpc₁ : ContinuousOn p₁ (Icc s t)) (hpc₂ : ContinuousOn p₂ (Icc s t))
    (hr₁ : ContinuousOn r₁ (Icc s t)) (hr₂ : ContinuousOn r₂ (Icc s t)) :
    |∫ r in s..t, σ r * (f₁ r * f₂ r)|
      ≤ |σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (f₁ t * u₂ t)
          - σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (u₁ t * f₂ t)
          - (σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (f₁ s * u₂ s)
          - σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (u₁ s * f₂ s))|
        + |∫ r in s..t, α r * (f₁ r * u₂ r)| + |∫ r in s..t, β r * (u₁ r * f₂ r)|
        + |∫ r in s..t, σ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (p₁ r * f₁ r * r₂ r - p₂ r * r₁ r * f₂ r)| := by
  rw [Cvs.Upstream.SturmCrossIdentitySources.integral_cross_src hst hp₁ hp₂ hD hf₁ hu₁ hf₂ hu₂ hA hB hαc hβc hσc hq₁ hq₂
    hpc₁ hpc₂ hr₁ hr₂]
  set X := σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (f₁ t * u₂ t)
    - σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (u₁ t * f₂ t)
    - (σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (f₁ s * u₂ s)
    - σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (u₁ s * f₂ s))
  set Y := ∫ r in s..t, α r * (f₁ r * u₂ r)
  set Z := ∫ r in s..t, β r * (u₁ r * f₂ r)
  set W := ∫ r in s..t, σ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (p₁ r * f₁ r * r₂ r - p₂ r * r₁ r * f₂ r)
  calc |X - Y + Z - W| ≤ |X - Y + Z| + |W| := abs_sub _ _
    _ ≤ |X - Y| + |Z| + |W| := by linarith [abs_add_le (X - Y) Z]
    _ ≤ |X| + |Y| + |Z| + |W| := by linarith [abs_sub X Y]

end Cvs.L2a.CrossIntegralAbsBound
