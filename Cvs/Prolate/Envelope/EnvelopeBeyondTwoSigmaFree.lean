import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.L2a.TwoProlateCrossBound
import Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi
import Cvs.Prolate.Envelope.ProlateWeightToEdge
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ModeSmoothWeightByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Prolate envelopes beyond `ξ = 2` without `σ`

For `ξ ≥ 2` and `0 ≤ χ ≤ c²`, `p ≥ (3/4)ξ²` and `q ≥ (3/4)c²ξ²`, so `a = √(pq) ≥ (3/4)cξ²` whatever `σ = √(c² − χ)`:
`ψ² ≤ G/((3/4)cξ²)`, `|ψ_a(ξ₁)u_b(ξ₂)| ≤ (2/√3)G ξ₂/ξ₁`, and the non-resonant and resonant pairs of Cvs.L2a.TwoProlateResonantPairs hold with
`2/√3` for `√κ_m` and `(3/4)c` for `α_m`, for every `χ < c²`.
-/

namespace Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.TwoProlateCrossBound

/-- **`a ≥ (3/4)cξ²`** for `ξ ≥ 2`, `0 ≤ χ ≤ c²`. -/
theorem aP_ge {c χ ξ : ℝ} (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hξ : 2 ≤ ξ) : 3 / 4 * c * ξ ^ 2 ≤ aP c χ ξ := by
  unfold aP pP qP
  apply Real.le_sqrt_of_sq_le
  have hp : 3 / 4 * ξ ^ 2 ≤ ξ ^ 2 - 1 := by nlinarith
  have hq : 3 / 4 * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
  have := mul_le_mul hp hq (by positivity) (by nlinarith)
  nlinarith

/-- **`ψ² ≤ G/((3/4)cξ²)`** for `ξ ≥ 2`. -/
theorem psi_sq_le {c χ G ξ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hξ : 2 ≤ ξ)
    (hG : energy (aP c χ) ψ u ξ ≤ G) : ψ ξ ^ 2 ≤ G / (3 / 4 * c * ξ ^ 2) := by
  have ha := aP_ge hc hχc hξ
  have ha0 : 0 < 3 / 4 * c * ξ ^ 2 := by positivity
  have hapos : 0 < aP c χ ξ := lt_of_lt_of_le ha0 ha
  have hE : aP c χ ξ * ψ ξ ^ 2 ≤ G := by
    unfold energy at hG
    have : 0 ≤ u ξ ^ 2 / aP c χ ξ := by positivity
    linarith
  rw [le_div_iff₀ ha0]
  calc ψ ξ ^ 2 * (3 / 4 * c * ξ ^ 2) ≤ ψ ξ ^ 2 * aP c χ ξ := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
    _ ≤ G := by linarith

/-- **The cross envelope beyond `2`**: `|ψ_a(ξ₁)u_b(ξ₂)| ≤ G (2/√3) ξ₂/ξ₁`. -/
theorem cross_env_c {c χa χb G ξ₁ ξ₂ : ℝ} {ψa ua ψb ub : ℝ → ℝ} (hc : 0 < c)
    (hχa : χa < c ^ 2) (hχb0 : 0 ≤ χb) (hχb : χb < c ^ 2)
    (h₁ : 2 ≤ ξ₁) (h₂ : 2 ≤ ξ₂) (hGa : energy (aP c χa) ψa ua ξ₁ ≤ G) (hGb : energy (aP c χb) ψb ub ξ₂ ≤ G) :
    |ψa ξ₁ * ub ξ₂| ≤ G * (2 / √3) * (ξ₂ / ξ₁) := by
  have hξ₁ : 0 < ξ₁ := by linarith
  have hξ₂ : 0 < ξ₂ := by linarith
  have e1 := psi_sq_le hc hχa.le h₁ hGa
  have e2 := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.flux_sq_le hc hχb0 hχb (by linarith) hGb
  have hG : 0 ≤ G := by
    have := two_mul_abs_le_energy (ψ := ψa) (u := ua) (aP_pos (by linarith : (1 : ℝ) < ξ₁) (by positivity) hχa)
    linarith [abs_nonneg (ψa ξ₁ * ua ξ₁)]
  have hew : ew ξ₂ ≤ ξ₂ ^ 2 := by
    unfold ew
    have : √(ξ₂ ^ 2 - 1) ≤ ξ₂ := by rw [sqrt_le_left hξ₂.le]; linarith
    nlinarith
  have hs3 : 0 < √3 := by positivity
  have hsq : (ψa ξ₁ * ub ξ₂) ^ 2 ≤ (G * (2 / √3) * (ξ₂ / ξ₁)) ^ 2 := by
    have h33 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
    calc (ψa ξ₁ * ub ξ₂) ^ 2 = ψa ξ₁ ^ 2 * ub ξ₂ ^ 2 := by ring
      _ ≤ G / (3 / 4 * c * ξ₁ ^ 2) * (c * ew ξ₂ * G) := mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
      _ ≤ G / (3 / 4 * c * ξ₁ ^ 2) * (c * ξ₂ ^ 2 * G) := by gcongr
      _ = (G * (2 / √3) * (ξ₂ / ξ₁)) ^ 2 := by field_simp; rw [h33]; ring
  exact abs_le_of_sq_le_sq' hsq (by positivity) |> fun h => abs_le.mpr h

set_option maxHeartbeats 1000000 in
/-- **The non-stationary pair of two prolates, `σ`-free.** -/
theorem pair_c_le {c χ₁ χ₂ G Ξ m₁ m₂ s T : ℝ} {ψ₁ u₁ ψ₂ u₂ : ℝ → ℝ} (hc : 0 < c)
    (hχ₁0 : 0 ≤ χ₁) (hχ₁ : χ₁ < c ^ 2) (hχ₂0 : 0 ≤ χ₂) (hχ₂ : χ₂ < c ^ 2)
    (hm₂ : 0 < m₂) (h12 : m₂ < m₁) (hs : 2 ≤ m₂ * s) (hsT : s ≤ T) (hT : m₁ * T ≤ Ξ)
    (hΔ : |χ₂ - χ₁| ≤ (m₁ ^ 2 - m₂ ^ 2) * c ^ 2 * s ^ 2 / 4)
    (hψ₁ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψ₁ (u₁ ξ / pP ξ) ξ)
    (hu₁ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt u₁ (-(qP c χ₁ ξ * ψ₁ ξ)) ξ)
    (hψ₂ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψ₂ (u₂ ξ / pP ξ) ξ)
    (hu₂ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt u₂ (-(qP c χ₂ ξ * ψ₂ ξ)) ξ)
    (hG₁ : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χ₁) ψ₁ u₁ ξ ≤ G) (hG₂ : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χ₂) ψ₂ u₂ ξ ≤ G) :
    |∫ t in s..T, ψ₁ (m₁ * t) * ψ₂ (m₂ * t)|
      ≤ 8 * G * (2 / √3) / (c ^ 2 * s ^ 2 * (m₁ * m₂ * (m₁ - m₂))) := by
  have hm₁ : 0 < m₁ := hm₂.trans h12
  have hs0 : 0 < s := by by_contra h; push Not at h; nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  set κ := (2 / √3) ^ 2 with hκ
  have hκ0 : 0 ≤ √κ := sqrt_nonneg _
  have hκs : √κ = 2 / √3 := sqrt_sq (by positivity)
  have hG : 0 ≤ G := by
    have h2 : (2 : ℝ) ∈ Icc 2 Ξ := ⟨le_rfl, by nlinarith [hsT]⟩
    have ha := aP_pos (by norm_num : (1 : ℝ) < 2) hc2 hχ₁
    have := two_mul_abs_le_energy (ψ := ψ₁) (u := u₁) ha
    linarith [hG₁ 2 h2, abs_nonneg (ψ₁ 2 * u₁ 2)]
  have in2 : ∀ τ ∈ Icc s T, m₂ * τ ∈ Icc 2 Ξ := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2, hτ.1]⟩
  have in1 : ∀ τ ∈ Icc s T, m₁ * τ ∈ Icc 2 Ξ := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  -- `D₂ ≥ (m₁² − m₂²) c² τ⁴/4`
  have hE : ∀ τ ∈ Icc s T, c ^ 2 * τ ^ 4 / 2 ≤
      c ^ 2 * τ ^ 2 * (τ ^ 2 - 1 / m₂ ^ 2 - 1 / m₁ ^ 2) + χ₁ / (m₁ ^ 2 * m₂ ^ 2) := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h2 : 2 ≤ m₂ * τ := le_trans hs (by nlinarith [hτ.1])
    have e2 : 1 / m₂ ^ 2 ≤ τ ^ 2 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have e1 : 1 / m₁ ^ 2 ≤ 1 / m₂ ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have : 0 ≤ χ₁ / (m₁ ^ 2 * m₂ ^ 2) := by positivity
    have : c ^ 2 * τ ^ 2 * (τ ^ 2 / 2) ≤ c ^ 2 * τ ^ 2 * (τ ^ 2 - 1 / m₂ ^ 2 - 1 / m₁ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hd12 : 0 < m₁ ^ 2 - m₂ ^ 2 := by nlinarith
  have hD : ∀ τ ∈ Icc s T, (m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * τ ^ 4 / 4) ≤ Dmr2 c χ₁ χ₂ m₁ m₂ τ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have e : Dmr2 c χ₁ χ₂ m₁ m₂ τ = Dmr c χ₁ m₁ m₂ τ + pm m₁ τ * (χ₂ - χ₁) := by
      unfold Dmr2 Dmr qm; ring
    rw [e, Cvs.L2a.NonstationaryCrossPairClosed.Dmr_eq hm₁.ne' hm₂.ne']
    have hp0 : 0 ≤ pm m₁ τ := by
      have h2 : 2 ≤ m₂ * τ := le_trans hs (by nlinarith [hτ.1])
      have h3 : m₂ * τ ≤ m₁ * τ := mul_le_mul_of_nonneg_right h12.le hτ0.le
      unfold pm; apply div_nonneg _ (by positivity); nlinarith
    have hp1 : pm m₁ τ ≤ τ ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
    have hlow : -(pm m₁ τ * |χ₂ - χ₁|) ≤ pm m₁ τ * (χ₂ - χ₁) := by
      have := neg_abs_le (χ₂ - χ₁); nlinarith
    have hsτ : s ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hs0.le hτ.1 2
    have h1 : pm m₁ τ * |χ₂ - χ₁| ≤ τ ^ 2 * ((m₁ ^ 2 - m₂ ^ 2) * c ^ 2 * s ^ 2 / 4) :=
      mul_le_mul hp1 hΔ (abs_nonneg _) (by positivity)
    have h2 : τ ^ 2 * ((m₁ ^ 2 - m₂ ^ 2) * c ^ 2 * s ^ 2 / 4) ≤ (m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * τ ^ 4 / 4) := by
      have := mul_le_mul_of_nonneg_left hsτ (by positivity : (0 : ℝ) ≤ τ ^ 2 * (m₁ ^ 2 - m₂ ^ 2) * c ^ 2 / 4)
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left (hE τ hτ) hd12.le
    nlinarith
  have hDpos : ∀ τ ∈ Icc s T, 0 < Dmr2 c χ₁ χ₂ m₁ m₂ τ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    exact lt_of_lt_of_le (by positivity) (hD τ hτ)
  -- the cross sups
  have hZ : ∀ τ ∈ Icc s T, |ψ₁ (m₁ * τ) * (u₂ (m₂ * τ) / m₂)| ≤ G * √κ / m₁ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h := cross_env_c hc hχ₁ hχ₂0 hχ₂ (in1 τ hτ).1 (in2 τ hτ).1
      (hG₁ _ (in1 τ hτ)) (hG₂ _ (in2 τ hτ))
    rw [← hκs] at h
    rw [show ψ₁ (m₁ * τ) * (u₂ (m₂ * τ) / m₂) = ψ₁ (m₁ * τ) * u₂ (m₂ * τ) / m₂ by ring, abs_div,
      abs_of_pos hm₂, div_le_iff₀ hm₂]
    calc |ψ₁ (m₁ * τ) * u₂ (m₂ * τ)| ≤ G * √κ * (m₂ * τ / (m₁ * τ)) := h
      _ = G * √κ / m₁ * m₂ := by field_simp
  have hV : ∀ τ ∈ Icc s T, |u₁ (m₁ * τ) / m₁ * ψ₂ (m₂ * τ)| ≤ G * √κ / m₂ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h := cross_env_c hc hχ₂ hχ₁0 hχ₁ (in2 τ hτ).1 (in1 τ hτ).1
      (hG₂ _ (in2 τ hτ)) (hG₁ _ (in1 τ hτ))
    rw [← hκs] at h
    rw [show u₁ (m₁ * τ) / m₁ * ψ₂ (m₂ * τ) = ψ₂ (m₂ * τ) * u₁ (m₁ * τ) / m₁ by ring, abs_div,
      abs_of_pos hm₁, div_le_iff₀ hm₁]
    calc |ψ₂ (m₂ * τ) * u₁ (m₁ * τ)| ≤ G * √κ * (m₁ * τ / (m₂ * τ)) := h
      _ = G * √κ / m₂ * m₁ := by field_simp
  have key := prolate_cross2_le (c := c) (χ := χ₁) (χ' := χ₂) (m := m₁) (r := m₂)
    (f₁ := fun t => ψ₁ (m₁ * t)) (u₁ := fun t => u₁ (m₁ * t) / m₁)
    (f₂ := fun t => ψ₂ (m₂ * t)) (u₂ := fun t => u₂ (m₂ * t) / m₂) hsT hm₂ h12 (by linarith) hχ₁ hχ₂ hDpos
    (fun τ hτ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm₁ (hψ₁ _ (in1 τ hτ)) (hu₁ _ (in1 τ hτ))).1)
    (fun τ hτ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm₁ (hψ₁ _ (in1 τ hτ)) (hu₁ _ (in1 τ hτ))).2)
    (fun τ hτ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm₂ (hψ₂ _ (in2 τ hτ)) (hu₂ _ (in2 τ hτ))).1)
    (fun τ hτ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm₂ (hψ₂ _ (in2 τ hτ)) (hu₂ _ (in2 τ hτ))).2) hZ hV
  -- closed form
  have hDs := hD s (left_mem_Icc.mpr hsT)
  have hp1 : pm m₁ s ≤ s ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hp2 : pm m₂ s ≤ s ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hnum : 2 * (pm m₁ s * (G * √κ / m₁) + pm m₂ s * (G * √κ / m₂))
      ≤ 2 * (s ^ 2 * (G * √κ / m₁) + s ^ 2 * (G * √κ / m₂)) := by
    have : 0 ≤ G * √κ / m₁ := by positivity
    have : 0 ≤ G * √κ / m₂ := by positivity
    nlinarith
  have hDpos' : 0 < (m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * s ^ 4 / 4) := by positivity
  calc |∫ t in s..T, ψ₁ (m₁ * t) * ψ₂ (m₂ * t)|
      ≤ 2 * (pm m₁ s * (G * √κ / m₁) + pm m₂ s * (G * √κ / m₂)) / Dmr2 c χ₁ χ₂ m₁ m₂ s := key
    _ ≤ 2 * (s ^ 2 * (G * √κ / m₁) + s ^ 2 * (G * √κ / m₂)) / ((m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * s ^ 4 / 4)) := by
        apply div_le_div₀ (by positivity) hnum hDpos' hDs
    _ = 8 * G * √κ / (c ^ 2 * s ^ 2 * (m₁ * m₂ * (m₁ - m₂))) := by
        have : m₁ - m₂ ≠ 0 := by linarith
        have : m₁ ^ 2 - m₂ ^ 2 ≠ 0 := by nlinarith
        have : -m₂ ^ 2 + m₁ ^ 2 ≠ 0 := by nlinarith
        field_simp; ring
    _ = 8 * G * (2 / √3) / (c ^ 2 * s ^ 2 * (m₁ * m₂ * (m₁ - m₂))) := by rw [hκs]

/-- **A non-resonant pair of two prolates, `σ`-free**, `m, n ≥ 2`, `|m − n| ≥ 1`. -/
theorem nonres_c_le {c χa χb G Ξ m n T : ℝ} {ψa ua ψb ub : ℝ → ℝ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχa : χa < c ^ 2) (hχb0 : 0 ≤ χb) (hχb : χb < c ^ 2)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : 1 ≤ |m - n|) (hT : 1 ≤ T) (hmT : m * T ≤ Ξ) (hnT : n * T ≤ Ξ)
    (hψa : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χb) ψb ub ξ ≤ G) :
    |∫ θ in (1 : ℝ)..T, ψa (m * θ) * ψb (n * θ)|
      ≤ 8 * G * (2 / √3) / (c ^ 2 * (m * n * |m - n|)) := by
  have hΔ : |χb - χa| ≤ c ^ 2 := by
    rw [abs_le]; constructor <;> linarith
  rcases lt_or_gt_of_ne (show m ≠ n by intro h; rw [h, sub_self, abs_zero] at hmn; linarith) with h | h
  · have hsep : 1 ≤ n - m := by rw [abs_sub_comm, abs_of_pos (by linarith)] at hmn; exact hmn
    have hΔ' : |χa - χb| ≤ (n ^ 2 - m ^ 2) * c ^ 2 * 1 ^ 2 / 4 := by
      rw [abs_sub_comm]; refine hΔ.trans ?_
      have : 4 ≤ n ^ 2 - m ^ 2 := by nlinarith
      nlinarith [sq_nonneg c]
    have key := pair_c_le hc hχb0 hχb hχa0 hχa (by linarith : (0:ℝ) < m) h (by linarith) hT hnT hΔ'
      hψb hub hψa hua hGb hGa
    have e : ∫ θ in (1 : ℝ)..T, ψa (m * θ) * ψb (n * θ) = ∫ θ in (1 : ℝ)..T, ψb (n * θ) * ψa (m * θ) := by
      congr 1; funext θ; ring
    rw [e, abs_of_neg (by linarith : m - n < 0)]
    simp only [one_pow, mul_one] at key
    convert key using 3; ring
  · have hsep : 1 ≤ m - n := by rw [abs_of_pos (by linarith)] at hmn; exact hmn
    have hΔ' : |χb - χa| ≤ (m ^ 2 - n ^ 2) * c ^ 2 * 1 ^ 2 / 4 := by
      refine hΔ.trans ?_
      have : 4 ≤ m ^ 2 - n ^ 2 := by nlinarith
      nlinarith [sq_nonneg c]
    have key := pair_c_le hc hχa0 hχa hχb0 hχb (by linarith : (0:ℝ) < n) h (by linarith) hT hmT hΔ'
      hψa hua hψb hub hGa hGb
    rw [abs_of_pos (by linarith : 0 < m - n)]
    simp only [one_pow, mul_one] at key
    exact key

/-- **The resonant pair of two prolates, `σ`-free**: at most `G/((3/4)c n²)`, `n ≥ 2`. -/
theorem resonant_c_le {c χa χb G n s : ℝ} {ψa ua ψb ub : ℝ → ℝ} (hc : 0 < c)
    (hχa : χa ≤ c ^ 2) (hχb : χb ≤ c ^ 2)
    (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hGa : ∀ ξ ∈ Icc n (n * s), energy (aP c χa) ψa ua ξ ≤ G)
    (hGb : ∀ ξ ∈ Icc n (n * s), energy (aP c χb) ψb ub ξ ≤ G) (hG0 : 0 ≤ G) :
    |∫ θ in (1 : ℝ)..s, ψa (n * θ) * ψb (n * θ)| ≤ G / (3 / 4 * c * n ^ 2) := by
  set α := 3 / 4 * c with hα
  have hα0 : 0 < α := by positivity
  have hn0 : 0 < n := by linarith
  have hmem : ∀ θ ∈ Icc (1 : ℝ) s, n * θ ∈ Icc n (n * s) := fun θ hθ =>
    ⟨by nlinarith [hθ.1], mul_le_mul_of_nonneg_left hθ.2 hn0.le⟩
  have sq_le : ∀ {χ : ℝ} {ψ u : ℝ → ℝ}, χ ≤ c ^ 2 → ∀ ξ, 2 ≤ ξ → energy (aP c χ) ψ u ξ ≤ G →
      ψ ξ ^ 2 ≤ G / (α * ξ ^ 2) := fun {χ ψ u} hm ξ hξ hG => psi_sq_le hc hm hξ hG
  have hpt : ∀ θ ∈ Ioc (1 : ℝ) s, ‖ψa (n * θ) * ψb (n * θ)‖ ≤ G / (α * n ^ 2) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ' : θ ∈ Icc (1 : ℝ) s := ⟨hθ.1.le, hθ.2⟩
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have hξ : 2 ≤ n * θ := by nlinarith [hθ.1]
    have ha := sq_le hχa _ hξ (hGa _ (hmem θ hθ'))
    have hb := sq_le hχb _ hξ (hGb _ (hmem θ hθ'))
    rw [Real.norm_eq_abs, abs_mul]
    have hab : |ψa (n * θ)| * |ψb (n * θ)| ≤ (ψa (n * θ) ^ 2 + ψb (n * θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|ψa (n * θ)| - |ψb (n * θ)|), sq_abs (ψa (n * θ)), sq_abs (ψb (n * θ))]
    calc |ψa (n * θ)| * |ψb (n * θ)| ≤ (ψa (n * θ) ^ 2 + ψb (n * θ) ^ 2) / 2 := hab
      _ ≤ G / (α * (n * θ) ^ 2) := by linarith
      _ = G / (α * n ^ 2) * (1 / θ ^ 2) := by field_simp
  have hint : IntervalIntegrable (fun θ : ℝ => G / (α * n ^ 2) * (1 / θ ^ 2)) MeasureTheory.volume 1 s :=
    (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2)
      (fun θ hθ => pow_ne_zero 2 (by rw [uIcc_of_le hs] at hθ; linarith [hθ.1] : (0:ℝ) < θ).ne'))).intervalIntegrable
  have key := intervalIntegral.norm_integral_le_of_norm_le hs (MeasureTheory.ae_of_all _ hpt) hint
  rw [Real.norm_eq_abs] at key
  calc |∫ θ in (1 : ℝ)..s, ψa (n * θ) * ψb (n * θ)| ≤ ∫ θ in (1 : ℝ)..s, G / (α * n ^ 2) * (1 / θ ^ 2) := key
    _ = G / (α * n ^ 2) * (1 - 1 / s) := by
        rw [intervalIntegral.integral_const_mul, Cvs.Prolate.ModeSmoothWeightByParts.integral_inv_sq one_pos hs]; ring
    _ ≤ G / (α * n ^ 2) := by
        have hs0 : (0:ℝ) < s := by linarith
        have : 0 ≤ 1 / s := by positivity
        have hG' : 0 ≤ G / (α * n ^ 2) := by positivity
        nlinarith

end Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree
