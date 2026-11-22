import Mathlib
import Cvs.Prolate.PruferWindowPair
import Cvs.Upstream.FirstDerivativeTestVariation
import Cvs.Upstream.SecondDerivativeWindowTest

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit envelope of a rung pair from its Prüfer data

On an ordered window `[p, q]` a rung pair `ψᵢ(m·)ψⱼ(m′·)` in Prüfer form is bounded by the window test on the
difference phase (a stationary window `[c₁, c₂]` of width `2δ`, `|φ⁻'| ≥ λδ` outside it, `∫|φ⁻''| ≤ W⁻`) plus the
first-derivative test on the sum phase (`|φ⁺'| ≥ μ` of one sign, `∫|φ⁺''| ≤ W⁺`), both with the amplitude product
`B = AᵢAⱼ/2` bounded by `A` and of variation at most `V`: the envelope `E(i, j, m, m′)` of an earlier result in closed form.
-/

namespace Cvs.Prolate.Envelope.RungPairPruferEnvelope

open Real Set MeasureTheory intervalIntegral
open Cvs.Upstream.FirstDerivativeTestVariation Cvs.Upstream.SecondDerivativeWindowTest Cvs.Prolate.PruferWindowPair

/-- The explicit envelope: `2δA + 2(2A + V)/(λδ) + 2AW⁻/(λδ)² + (2A + V)/μ + AW⁺/μ²`. -/
noncomputable def envelope (lam δ μ A V Wd Ws : ℝ) : ℝ :=
  2 * δ * A + 2 * ((2 * A + V) / (lam * δ)) + 2 * (A * Wd / (lam * δ) ^ 2) + ((2 * A + V) / μ + A * Ws / μ ^ 2)

/-- **The envelope of a rung pair from its Prüfer data** on an ordered window `[p, q]`. -/
theorem pair_le_envelope {ψi ψj Ai Aj Θi Θj B B₁ φd φd₁ φd₂ φs φs₁ φs₂ : ℝ → ℝ}
    {m m' p q c₁ c₂ lam δ μ A V Wd Ws : ℝ}
    (hpc : p ≤ c₁) (hcc : c₁ ≤ c₂) (hcq : c₂ ≤ q) (hlam : 0 < lam) (hδ : 0 < δ) (hμ : 0 < μ)
    (hwidth : c₂ - c₁ ≤ 2 * δ)
    (hi : ∀ t ∈ Icc p q, ψi (m * t) = Ai (m * t) * Real.cos (Θi (m * t)))
    (hj : ∀ t ∈ Icc p q, ψj (m' * t) = Aj (m' * t) * Real.cos (Θj (m' * t)))
    (hB : ∀ t, B t = Ai (m * t) * Aj (m' * t) / 2)
    (hφd : ∀ t, φd t = Θi (m * t) - Θj (m' * t)) (hφs : ∀ t, φs t = Θi (m * t) + Θj (m' * t))
    (hBd : ∀ t ∈ Icc p q, HasDerivAt B (B₁ t) t) (hB₁c : ContinuousOn B₁ (Icc p q))
    (hA : ∀ t ∈ Icc p q, |B t| ≤ A) (hV : ∫ t in p..q, |B₁ t| ≤ V)
    (hφd' : ∀ t ∈ Icc p q, HasDerivAt φd (φd₁ t) t) (hφd₁ : ∀ t ∈ Icc p q, HasDerivAt φd₁ (φd₂ t) t)
    (hφd₂c : ContinuousOn φd₂ (Icc p q))
    (hleft : ∀ t ∈ Icc p c₁, φd₁ t ≤ -(lam * δ)) (hright : ∀ t ∈ Icc c₂ q, lam * δ ≤ φd₁ t)
    (hWd : ∫ t in p..q, |φd₂ t| ≤ Wd)
    (hφs' : ∀ t ∈ Icc p q, HasDerivAt φs (φs₁ t) t) (hφs₁ : ∀ t ∈ Icc p q, HasDerivAt φs₁ (φs₂ t) t)
    (hφs₂c : ContinuousOn φs₂ (Icc p q))
    (hsign : (∀ t ∈ Icc p q, μ ≤ φs₁ t) ∨ (∀ t ∈ Icc p q, φs₁ t ≤ -μ))
    (hWs : ∫ t in p..q, |φs₂ t| ≤ Ws) :
    |∫ t in p..q, ψi (m * t) * ψj (m' * t)| ≤ envelope lam δ μ A V Wd Ws := by
  have hpq : p ≤ q := hpc.trans (hcc.trans hcq)
  -- the two oscillatory integrals in terms of `B`, `φd`, `φs`
  have eB : ∀ t, Ai (m * t) * Aj (m' * t) / 2 = B t := fun t => (hB t).symm
  have ed : (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) - Θj (m' * t)))
      = fun t => B t * Real.cos (φd t) := by
    funext t; rw [eB t, hφd t]
  have es : (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) + Θj (m' * t)))
      = fun t => B t * Real.cos (φs t) := by
    funext t; rw [eB t, hφs t]
  -- continuity, hence interval integrability
  have hBc : ContinuousOn B (Icc p q) := fun t ht => (hBd t ht).continuousAt.continuousWithinAt
  have hφdc : ContinuousOn φd (Icc p q) := fun t ht => (hφd' t ht).continuousAt.continuousWithinAt
  have hφsc : ContinuousOn φs (Icc p q) := fun t ht => (hφs' t ht).continuousAt.continuousWithinAt
  have hId : IntervalIntegrable (fun t => B t * Real.cos (φd t)) volume p q :=
    (hBc.mul (Real.continuous_cos.comp_continuousOn hφdc)).intervalIntegrable_of_Icc hpq
  have hIs : IntervalIntegrable (fun t => B t * Real.cos (φs t)) volume p q :=
    (hBc.mul (Real.continuous_cos.comp_continuousOn hφsc)).intervalIntegrable_of_Icc hpq
  -- the difference phase by the window test, the sum phase by the first-derivative test
  have hd := window_test_var hpc hcc hcq hlam hδ hwidth hBd hφd' hφd₁ hleft hright hφd₂c hB₁c hA hV hWd
  have hs := piece_le_var hpq hμ hBd hφs' hφs₁ hsign hφs₂c hB₁c hA hV hWs
  have := pair_interval_le (Ed := 2 * δ * A + 2 * ((2 * A + V) / (lam * δ)) + 2 * (A * Wd / (lam * δ) ^ 2))
    (Es := (2 * A + V) / μ + A * Ws / μ ^ 2) hpq hi hj (by rw [ed]; exact hId) (by rw [es]; exact hIs)
    (by rw [ed]; exact hd) (by rw [es]; exact hs)
  unfold envelope
  exact this

end Cvs.Prolate.Envelope.RungPairPruferEnvelope
