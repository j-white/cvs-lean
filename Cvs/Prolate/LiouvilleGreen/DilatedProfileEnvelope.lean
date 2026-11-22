import Mathlib
import Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct
import Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.NonstationaryProfilePairing
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The envelope of a dilated-mode profile pairing

For the mode `ψ(m·)` of a prolate rung in Prüfer form against `cos(cm′t)/(m′t)^{n+1}` on `[p, q]` with `mp ≥ ξ₀` and
`m′ > mU(ξ₀)`, neither phase has a stationary point, and the pairing is at most
`(2A + V)/μ⁻ + AW/μ⁻² + (2A + V)/μ⁺ + AW/μ⁺²` with `μ⁻ = c(m′ − mU(ξ₀))`, `μ⁺ = c(m′ + m(1 − ξ₀/(c(ξ₀² − 1))))`
(Cvs.Prolate.LiouvilleGreen.NonstationaryProfilePairing), `A` of Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct, `V` any bound on the amplitude product's variation (Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeVariation) and `W` on `∫|m²Θ''(m·)|`.
-/

namespace Cvs.Prolate.LiouvilleGreen.DilatedProfileEnvelope

open Real Set MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.NonstationaryProfilePairing Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeVariation

/-- **The envelope of a dilated-mode profile pairing.** -/
theorem dilated_pair_le {c χ ξ₀ ξ₁ p q V W : ℝ} {m m' n : ℕ} {ψ u Θ rate' : ℝ → ℝ}
    (h0 : 1 < ξ₀) (hm : 1 ≤ m) (hp : ξ₀ ≤ m * p) (hpq : p ≤ q) (hq : (m : ℝ) * q ≤ ξ₁)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hs : ξ₀ / (c * (ξ₀ ^ 2 - 1)) ≤ 1) (hW0 : wP c χ ξ₀ < 2) (hsep : (m : ℝ) * U c ξ₀ < m')
    (hψ : ∀ s ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u s / pP s) s)
    (hu : ∀ s ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ s * ψ s)) s)
    (hE : ∀ t ∈ Icc p q, 0 < energy (aP c χ) ψ u ((m : ℝ) * t))
    (hprufer : ∀ t ∈ Icc p q, ψ ((m : ℝ) * t) = ampl (aP c χ) ψ u ((m : ℝ) * t) * Real.cos (Θ ((m : ℝ) * t)))
    (hΘ : ∀ t ∈ Icc p q, HasDerivAt Θ (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t)) ((m : ℝ) * t))
    (hrate : ∀ t ∈ Icc p q, HasDerivAt (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u) (rate' ((m : ℝ) * t)) ((m : ℝ) * t))
    (hrate'c : ContinuousOn (fun t => (m : ℝ) * (m * rate' ((m : ℝ) * t))) (Icc p q))
    (hB₁c : ContinuousOn (profAmpM' c χ ψ u m m' n) (Icc p q))
    (hV : ∫ t in p..q, |profAmpM' c χ ψ u m m' n t| ≤ V)
    (hW : ∫ t in p..q, |(m : ℝ) * (m * rate' ((m : ℝ) * t))| ≤ W) :
    |∫ t in p..q, ψ ((m : ℝ) * t) * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1))|
      ≤ envelope2 (c * (m' - m * U c ξ₀)) (c * (m' + m * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)))))
          (ampBoundM c χ ψ u ξ₀ p m m' n) V W W := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hmp1 : 1 < (m : ℝ) * p := lt_of_lt_of_le h0 hp
  have hp0 : 0 < p := by
    by_contra h; push Not at h
    have : (m : ℝ) * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0.le h
    linarith
  have hμm : 0 < c * (m' - m * U c ξ₀) := mul_pos hc (by linarith)
  have hμp : 0 < c * (m' + m * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)))) := by
    have : 0 ≤ 1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)) := by linarith
    positivity
  obtain ⟨hdiff, hsum⟩ := profile_rates (m' := m') (ψ := ψ) (u := u) hm h0 hp hc hχ0 hχc hs hE
  have hswap : (fun t => ψ ((m : ℝ) * t) * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1)))
      = fun t => (fun x => Real.cos (c * x) / x ^ (n + 1)) ((m' : ℝ) * t) * ψ ((m : ℝ) * t) := by
    funext t; ring
  rw [show (∫ t in p..q, ψ ((m : ℝ) * t) * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1)))
      = ∫ t in p..q, (fun x => Real.cos (c * x) / x ^ (n + 1)) ((m' : ℝ) * t) * ψ ((m : ℝ) * t) by rw [hswap]]
  have hlin : ∀ t, HasDerivAt (fun t => (m : ℝ) * t) (m : ℝ) t := fun t => by
    simpa using (hasDerivAt_id t).const_mul (m : ℝ)
  have hlin' : ∀ t, HasDerivAt (fun t => c * ((m' : ℝ) * t)) (c * m') t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul (m' : ℝ)).const_mul c
  have hΘm : ∀ t ∈ Icc p q, HasDerivAt (fun t => Θ ((m : ℝ) * t))
      (m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t)) t := fun t ht => by
    have := (hΘ t ht).comp t (hlin t)
    exact this.congr_deriv (by ring)
  have hratem : ∀ t ∈ Icc p q, HasDerivAt (fun t => (m : ℝ) * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t))
      ((m : ℝ) * (m * rate' ((m : ℝ) * t))) t := fun t ht => by
    have := ((hrate t ht).comp t (hlin t)).const_mul (m : ℝ)
    exact this.congr_deriv (by ring)
  refine pair_le_envelope2 (ψi := fun x => Real.cos (c * x) / x ^ (n + 1)) (ψj := ψ) (m := (m' : ℝ)) (m' := (m : ℝ))
    (A := ampBoundM c χ ψ u ξ₀ p m m' n) (V := V) (Wm := W) (Wp := W)
    (Ai := fun x => 1 / x ^ (n + 1)) (Aj := ampl (aP c χ) ψ u) (Θi := fun x => c * x) (Θj := Θ)
    (B := profAmpM c χ ψ u m m' n) (B₁ := profAmpM' c χ ψ u m m' n)
    (φd := fun t => c * ((m' : ℝ) * t) - Θ ((m : ℝ) * t))
    (φd₁ := fun t => c * m' - m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t))
    (φd₂ := fun t => -((m : ℝ) * (m * rate' ((m : ℝ) * t))))
    (φs := fun t => c * ((m' : ℝ) * t) + Θ ((m : ℝ) * t))
    (φs₁ := fun t => c * m' + m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t))
    (φs₂ := fun t => (m : ℝ) * (m * rate' ((m : ℝ) * t)))
    hpq hμm hμp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have hx : (0 : ℝ) < (m' : ℝ) * t := mul_pos hm'0 (lt_of_lt_of_le hp0 ht.1)
    show Real.cos (c * ((m' : ℝ) * t)) / ((m' : ℝ) * t) ^ (n + 1)
      = 1 / ((m' : ℝ) * t) ^ (n + 1) * Real.cos (c * ((m' : ℝ) * t))
    field_simp
  · exact hprufer
  · intro t
    simp only [profAmpM]
    field_simp
  · intro t; rfl
  · intro t; rfl
  · intro t ht
    have hmt1 : 1 < (m : ℝ) * t := lt_of_lt_of_le hmp1 (mul_le_mul_of_nonneg_left ht.1 hm0.le)
    have ht0 : 0 < t := lt_of_lt_of_le hp0 ht.1
    have hmtI : (m : ℝ) * t ∈ Icc ξ₀ ξ₁ :=
      ⟨hp.trans (mul_le_mul_of_nonneg_left ht.1 hm0.le), (mul_le_mul_of_nonneg_left ht.2 hm0.le).trans hq⟩
    exact hasDerivAt_profAmpM hm hmt1 ht0 hc hχc hm' (hE t ht) (hψ _ hmtI) (hu _ hmtI)
  · exact hB₁c
  · intro t ht
    exact profAmpM_le h0 hm hp ht.1 ht.2 hq hc hχ0 hχc hm' hψ hu hW0
  · exact hV
  · intro t ht
    exact ((hlin' t).sub (hΘm t ht)).congr_deriv (by ring)
  · intro t ht
    exact ((hasDerivAt_const t (c * (m' : ℝ))).sub (hratem t ht)).congr_deriv (by ring)
  · exact hrate'c.neg
  · exact Or.inl (fun t ht => by have := hdiff t ht; linarith)
  · simp only [abs_neg]; exact hW
  · intro t ht
    exact ((hlin' t).add (hΘm t ht)).congr_deriv (by ring)
  · intro t ht
    exact ((hasDerivAt_const t (c * (m' : ℝ))).add (hratem t ht)).congr_deriv (by ring)
  · exact hrate'c
  · exact Or.inl (fun t ht => by have := hsum t ht; linarith)
  · exact hW

end Cvs.Prolate.LiouvilleGreen.DilatedProfileEnvelope
