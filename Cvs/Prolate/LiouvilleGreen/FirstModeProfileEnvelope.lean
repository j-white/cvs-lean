import Mathlib
import Cvs.Prolate.Envelope.RungPairPruferEnvelope
import Cvs.Prolate.LiouvilleGreen.FirstModeWindowData
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct
import Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The envelope of a first-mode profile pairing

For the first mode of a prolate rung in Prüfer form against the profile `cos(cm′t)/(m′t)^{n+1}`, on `[p, q]` beyond
`ξ₀` with the window `[c₁, c₂]` around the stationary point, the pairing is at most the envelope of Cvs.Prolate.Envelope.RungPairPruferEnvelope with
`δ = (c₂ − c₁)/2`, `λδ = min(L, R)` (Cvs.Prolate.LiouvilleGreen.FirstModeWindowData), `μ = c(m′ + 1 − ξ₀/(c(ξ₀² − 1)))`, the amplitude bound of Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct,
`V = (q − p)·D` from Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeVariation and `W = ∫_p^q |Θ''|`: every term a closed form in the coefficients but `W`.
-/

namespace Cvs.Prolate.LiouvilleGreen.FirstModeProfileEnvelope

open Real Set MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.Envelope.RungPairPruferEnvelope Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeVariation Cvs.Prolate.LiouvilleGreen.FirstModeWindowData

/-- The window half-width `(c₂ − c₁)/2`. -/
noncomputable def halfWidth (c₁ c₂ : ℝ) : ℝ := (c₂ - c₁) / 2

/-- **The envelope of a first-mode profile pairing.** -/
theorem profile_pair_le {c χ ξ₀ ξ₁ p c₁ c₂ q Δ W : ℝ} {m' n : ℕ} {ψ u Θ rate' : ℝ → ℝ}
    (h0 : 1 < ξ₀) (hp : ξ₀ ≤ p) (hpc : p ≤ c₁) (hcc : c₁ < c₂) (hcq : c₂ ≤ q) (hq : q ≤ ξ₁)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 2 ≤ m')
    (hΔ : 0 ≤ Δ) (hleft : c₁ ^ 2 ≤ statSq c χ m' - Δ) (hright : statSq c χ m' + Δ ≤ c₂ ^ 2)
    (hs : ξ₀ / (c * (ξ₀ ^ 2 - 1)) ≤ 1) (hW0 : wP c χ ξ₀ < 2)
    (hgap : 0 < min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m'))
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : ∀ t ∈ Icc p q, 0 < energy (aP c χ) ψ u t)
    (hprufer : ∀ t ∈ Icc p q, ψ t = ampl (aP c χ) ψ u t * Real.cos (Θ t))
    (hΘ : ∀ t ∈ Icc p q, HasDerivAt Θ (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t) t)
    (hrate : ∀ t ∈ Icc p q, HasDerivAt (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u) (rate' t) t)
    (hrate'c : ContinuousOn rate' (Icc p q))
    (hB₁c : ContinuousOn (profAmp' c χ ψ u m' n) (Icc p q))
    (hW : ∫ t in p..q, |rate' t| ≤ W) :
    |∫ t in p..q, ψ t * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1))|
      ≤ envelope (min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m') / halfWidth c₁ c₂) (halfWidth c₁ c₂)
          (c * (m' + 1 * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)))))
          (ampBound c χ ψ u ξ₀ p m' n) ((q - p) * derivBound c χ ψ u ξ₀ p m' n) W W := by
  have hp1 : 1 < p := lt_of_lt_of_le h0 hp
  have hpq : p ≤ q := hpc.trans (hcc.le.trans hcq)
  have hm0 : (0 : ℝ) < m' := by positivity
  have hm1 : 1 ≤ m' := le_trans (by norm_num) hm'
  have hδ : 0 < halfWidth c₁ c₂ := by unfold halfWidth; linarith
  have hlam : 0 < min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m') / halfWidth c₁ c₂ := div_pos hgap hδ
  have hμ : 0 < c * (m' + 1 * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)))) := by
    have : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
    have : 0 ≤ 1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)) := by linarith
    positivity
  obtain ⟨hwl, hwr, hws⟩ := window_rates (ψ := ψ) (u := u) h0 hp hpc hcc.le hcq hc hχ0 hχc hm' hΔ hleft hright hs hE
  -- the pairing as `ψi(m′·) ψj(1·)` with the profile first
  have hswap : (fun t => ψ t * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1)))
      = fun t => (fun x => Real.cos (c * x) / x ^ (n + 1)) ((m' : ℝ) * t) * ψ ((1 : ℝ) * t) := by
    funext t; simp only [one_mul]; ring
  rw [show (∫ t in p..q, ψ t * (Real.cos (c * (m' * t)) / (m' * t) ^ (n + 1)))
      = ∫ t in p..q, (fun x => Real.cos (c * x) / x ^ (n + 1)) ((m' : ℝ) * t) * ψ ((1 : ℝ) * t) by
      rw [hswap]]
  -- Cvs.Prolate.Envelope.RungPairPruferEnvelope with the profile as the first rung (`m := m′`) and the rung as the second (`m′ := 1`)
  refine pair_le_envelope (ψi := fun x => Real.cos (c * x) / x ^ (n + 1)) (ψj := ψ) (m := (m' : ℝ)) (m' := (1 : ℝ))
    (A := ampBound c χ ψ u ξ₀ p m' n) (V := (q - p) * derivBound c χ ψ u ξ₀ p m' n) (Wd := W) (Ws := W)
    (Ai := fun x => 1 / x ^ (n + 1)) (Aj := ampl (aP c χ) ψ u)
    (Θi := fun x => c * x) (Θj := Θ) (B := profAmp c χ ψ u m' n) (B₁ := profAmp' c χ ψ u m' n)
    (φd := fun t => c * ((m' : ℝ) * t) - Θ ((1 : ℝ) * t))
    (φd₁ := fun t => c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t) (φd₂ := fun t => -rate' t)
    (φs := fun t => c * ((m' : ℝ) * t) + Θ ((1 : ℝ) * t))
    (φs₁ := fun t => c * m' + rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t) (φs₂ := rate')
    hpc hcc.le hcq hlam hδ hμ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the window width
    unfold halfWidth; linarith
  · -- the profile in Prüfer form
    intro t ht
    have hx : (0 : ℝ) < (m' : ℝ) * t := by nlinarith [hp1, ht.1]
    show Real.cos (c * ((m' : ℝ) * t)) / ((m' : ℝ) * t) ^ (n + 1) = 1 / ((m' : ℝ) * t) ^ (n + 1) * Real.cos (c * ((m' : ℝ) * t))
    field_simp
  · -- the rung in Prüfer form
    intro t ht
    simp only [one_mul]
    exact hprufer t ht
  · -- `B = Ai(m′t) Aj(t)/2`
    intro t
    simp only [one_mul, profAmp]
    field_simp
  · intro t; simp only [one_mul]
  · intro t; simp only [one_mul]
  · -- `B` is differentiable
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hp1 ht.1
    have htI : t ∈ Icc ξ₀ ξ₁ := ⟨hp.trans ht.1, ht.2.trans hq⟩
    exact hasDerivAt_profAmp ht1 hc hχ0 hχc hm1 (hE t ht) (hψ t htI) (hu t htI)
  · exact hB₁c
  · -- `|B| ≤ A`
    intro t ht
    exact profAmp_le h0 hp ht.1 ht.2 hq hc hχ0 hχc hm1 hψ hu hW0
  · -- `∫|B'| ≤ (q − p) D`
    have hint : IntervalIntegrable (fun t => |profAmp' c χ ψ u m' n t|) volume p q :=
      hB₁c.abs.intervalIntegrable_of_Icc hpq
    calc ∫ t in p..q, |profAmp' c χ ψ u m' n t| ≤ ∫ t in p..q, derivBound c χ ψ u ξ₀ p m' n :=
          integral_mono_on hpq hint intervalIntegrable_const (fun t ht =>
            abs_profAmp'_le h0 hp ht.1 ht.2 hq hc hχ0 hχc hm1 hψ hu hW0 (hE t ht))
      _ = (q - p) * derivBound c χ ψ u ξ₀ p m' n := by rw [intervalIntegral.integral_const, smul_eq_mul]
  · -- the difference phase and its rate
    intro t ht
    have h1 : HasDerivAt (fun t => c * ((m' : ℝ) * t)) (c * m') t := by
      simpa using ((hasDerivAt_id t).const_mul (m' : ℝ)).const_mul c
    have h2 : HasDerivAt (fun t => Θ ((1 : ℝ) * t)) (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t) t := by
      simpa using hΘ t ht
    exact h1.sub h2
  · intro t ht
    have := hrate t ht
    exact ((hasDerivAt_const t (c * (m' : ℝ))).sub this).congr_deriv (by ring)
  · exact hrate'c.neg
  · -- left of the window
    intro t ht
    have := hwl t ht
    rw [div_mul_cancel₀ _ hδ.ne']
    exact this
  · intro t ht
    have := hwr t ht
    rw [div_mul_cancel₀ _ hδ.ne']
    exact this
  · -- `∫|φd''| ≤ W`
    simp only [abs_neg]; exact hW
  · -- the sum phase and its rate
    intro t ht
    have h1 : HasDerivAt (fun t => c * ((m' : ℝ) * t)) (c * m') t := by
      simpa using ((hasDerivAt_id t).const_mul (m' : ℝ)).const_mul c
    have h2 : HasDerivAt (fun t => Θ ((1 : ℝ) * t)) (rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t) t := by
      simpa using hΘ t ht
    exact h1.add h2
  · intro t ht
    exact ((hasDerivAt_const t (c * (m' : ℝ))).add (hrate t ht)).congr_deriv (by ring)
  · exact hrate'c
  · exact Or.inl (fun t ht => by have := hws t ht; linarith)
  · exact hW

end Cvs.Prolate.LiouvilleGreen.FirstModeProfileEnvelope
