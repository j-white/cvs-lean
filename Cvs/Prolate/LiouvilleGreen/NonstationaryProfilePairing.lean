import Mathlib
import Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PruferWindowPair
import Cvs.Upstream.FirstDerivativeTestVariation
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A profile pairing without a stationary point

When the difference phase `Θ(mt) − cm′t` keeps a rate of size at least `μ⁻` and the sum phase one of size at least
`μ⁺` on `[p, q]`, the pairing of the rung mode with `cos(cm′t)/(m′t)^{n+1}` is bounded by two first-derivative tests,
`(2A + V)/μ⁻ + AW⁻/μ⁻² + (2A + V)/μ⁺ + AW⁺/μ⁺²`; for a prolate rung with `mt ≥ ξ₀` and `m′ > m U(ξ₀)` the rates of
Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates give `μ⁻ = c(m′ − mU(ξ₀))` and `μ⁺ = c(m′ + m(1 − ξ₀/(c(ξ₀² − 1))))`.
-/

namespace Cvs.Prolate.LiouvilleGreen.NonstationaryProfilePairing

open Real Set MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Upstream.FirstDerivativeTestVariation Cvs.Prolate.PruferWindowPair Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates

/-- The envelope of a pairing whose two phases both pass the first-derivative test. -/
noncomputable def envelope2 (μm μp A V Wm Wp : ℝ) : ℝ :=
  (2 * A + V) / μm + A * Wm / μm ^ 2 + ((2 * A + V) / μp + A * Wp / μp ^ 2)

/-- **A pair whose two phases have no stationary point**: with `|φ⁻'| ≥ μ⁻` of one sign, `|φ⁺'| ≥ μ⁺` of one sign,
`|B| ≤ A`, `∫|B'| ≤ V`, `∫|φ⁻''| ≤ W⁻`, `∫|φ⁺''| ≤ W⁺`, the pair is at most `envelope2`. -/
theorem pair_le_envelope2 {ψi ψj Ai Aj Θi Θj B B₁ φd φd₁ φd₂ φs φs₁ φs₂ : ℝ → ℝ}
    {m m' p q μm μp A V Wm Wp : ℝ} (hpq : p ≤ q) (hμm : 0 < μm) (hμp : 0 < μp)
    (hi : ∀ t ∈ Icc p q, ψi (m * t) = Ai (m * t) * Real.cos (Θi (m * t)))
    (hj : ∀ t ∈ Icc p q, ψj (m' * t) = Aj (m' * t) * Real.cos (Θj (m' * t)))
    (hB : ∀ t, B t = Ai (m * t) * Aj (m' * t) / 2)
    (hφd : ∀ t, φd t = Θi (m * t) - Θj (m' * t)) (hφs : ∀ t, φs t = Θi (m * t) + Θj (m' * t))
    (hBd : ∀ t ∈ Icc p q, HasDerivAt B (B₁ t) t) (hB₁c : ContinuousOn B₁ (Icc p q))
    (hA : ∀ t ∈ Icc p q, |B t| ≤ A) (hV : ∫ t in p..q, |B₁ t| ≤ V)
    (hφd' : ∀ t ∈ Icc p q, HasDerivAt φd (φd₁ t) t) (hφd₁ : ∀ t ∈ Icc p q, HasDerivAt φd₁ (φd₂ t) t)
    (hφd₂c : ContinuousOn φd₂ (Icc p q))
    (hsignd : (∀ t ∈ Icc p q, μm ≤ φd₁ t) ∨ (∀ t ∈ Icc p q, φd₁ t ≤ -μm))
    (hWd : ∫ t in p..q, |φd₂ t| ≤ Wm)
    (hφs' : ∀ t ∈ Icc p q, HasDerivAt φs (φs₁ t) t) (hφs₁ : ∀ t ∈ Icc p q, HasDerivAt φs₁ (φs₂ t) t)
    (hφs₂c : ContinuousOn φs₂ (Icc p q))
    (hsigns : (∀ t ∈ Icc p q, μp ≤ φs₁ t) ∨ (∀ t ∈ Icc p q, φs₁ t ≤ -μp))
    (hWs : ∫ t in p..q, |φs₂ t| ≤ Wp) :
    |∫ t in p..q, ψi (m * t) * ψj (m' * t)| ≤ envelope2 μm μp A V Wm Wp := by
  have eB : ∀ t, Ai (m * t) * Aj (m' * t) / 2 = B t := fun t => (hB t).symm
  have ed : (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) - Θj (m' * t)))
      = fun t => B t * Real.cos (φd t) := by funext t; rw [eB t, hφd t]
  have es : (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) + Θj (m' * t)))
      = fun t => B t * Real.cos (φs t) := by funext t; rw [eB t, hφs t]
  have hBc : ContinuousOn B (Icc p q) := fun t ht => (hBd t ht).continuousAt.continuousWithinAt
  have hφdc : ContinuousOn φd (Icc p q) := fun t ht => (hφd' t ht).continuousAt.continuousWithinAt
  have hφsc : ContinuousOn φs (Icc p q) := fun t ht => (hφs' t ht).continuousAt.continuousWithinAt
  have hId : IntervalIntegrable (fun t => B t * Real.cos (φd t)) volume p q :=
    (hBc.mul (Real.continuous_cos.comp_continuousOn hφdc)).intervalIntegrable_of_Icc hpq
  have hIs : IntervalIntegrable (fun t => B t * Real.cos (φs t)) volume p q :=
    (hBc.mul (Real.continuous_cos.comp_continuousOn hφsc)).intervalIntegrable_of_Icc hpq
  have hd := piece_le_var hpq hμm hBd hφd' hφd₁ hsignd hφd₂c hB₁c hA hV hWd
  have hs := piece_le_var hpq hμp hBd hφs' hφs₁ hsigns hφs₂c hB₁c hA hV hWs
  have := pair_interval_le (Ed := (2 * A + V) / μm + A * Wm / μm ^ 2) (Es := (2 * A + V) / μp + A * Wp / μp ^ 2)
    hpq hi hj (by rw [ed]; exact hId) (by rw [es]; exact hIs) (by rw [ed]; exact hd)
    (by rw [es]; exact hs)
  unfold envelope2
  exact this

/-- **The rates of a prolate rung mode against a profile**, on an interval where `mt ≥ ξ₀` and the energy is
positive, with `ξ₀/(c(ξ₀² − 1)) ≤ 1`: the difference rate `m Θ'(mt) − cm′` is at most
`−c(m′ − mU(ξ₀))` and the sum rate at least `c(m′ + m(1 − ξ₀/(c(ξ₀² − 1))))`. -/
theorem profile_rates {c χ ξ₀ p q : ℝ} {m m' : ℕ} {ψ u : ℝ → ℝ} (hm : 1 ≤ m) (h0 : 1 < ξ₀)
    (hp : ξ₀ ≤ m * p) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hs : ξ₀ / (c * (ξ₀ ^ 2 - 1)) ≤ 1)
    (hE : ∀ t ∈ Icc p q, 0 < energy (aP c χ) ψ u (m * t)) :
    (∀ t ∈ Icc p q, m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * t) - c * m' ≤ -(c * (m' - m * U c ξ₀)))
      ∧ ∀ t ∈ Icc p q, c * (m' + m * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1))))
          ≤ m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * t) + c * m' := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · intro t ht
    have hθ : ξ₀ ≤ m * t := le_trans hp (mul_le_mul_of_nonneg_left ht.1 hm0.le)
    have := (dilate_rate_bounds (ψ := ψ) (u := u) hm h0 hθ hc hχ0 hχc hs (hE t ht)).2
    linarith
  · intro t ht
    have hθ : ξ₀ ≤ m * t := le_trans hp (mul_le_mul_of_nonneg_left ht.1 hm0.le)
    have := (dilate_rate_bounds (ψ := ψ) (u := u) hm h0 hθ hc hχ0 hχc hs (hE t ht)).1
    linarith

end Cvs.Prolate.LiouvilleGreen.NonstationaryProfilePairing
