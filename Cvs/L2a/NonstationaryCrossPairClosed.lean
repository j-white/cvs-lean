import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One non-stationary cross pair of prolate modes, in closed form

For a prolate solution `(ψ, u)` whose energy is at most `G_M` on `[2, Ξ]`, and modes `m₁ > m₂ > 0` on `[s, T]`
with `m₂ s ≥ 2`, `m₁T ≤ Ξ`: `|∫_s^T ψ(m₁t) ψ(m₂t) dt| ≤ 4 G_M √κ / (c² s² m₁ m₂ (m₁ − m₂))`.
-/

namespace Cvs.L2a.NonstationaryCrossPairClosed

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral

/-- **Scaling a prolate solution to a mode**: `ψ(m·)`, `u(m·)/m` solve the scaled system of mode `m`. -/
theorem scale_system {c χ m t : ℝ} {ψ u : ℝ → ℝ} (hm : 0 < m)
    (hψ : HasDerivAt ψ (u (m * t) / pP (m * t)) (m * t)) (hu : HasDerivAt u (-(qP c χ (m * t) * ψ (m * t))) (m * t)) :
    HasDerivAt (fun s => ψ (m * s)) ((u (m * t) / m) / pm m t) t ∧
      HasDerivAt (fun s => u (m * s) / m) (-(qm c χ m t * ψ (m * t))) t := by
  have hmt : HasDerivAt (fun s => m * s) m t := by simpa using (hasDerivAt_id t).const_mul m
  constructor
  · refine (hψ.comp t hmt).congr_deriv ?_
    unfold pm pP
    by_cases hp : m ^ 2 * t ^ 2 - 1 = 0
    · have : (m * t) ^ 2 - 1 = 0 := by nlinarith
      simp [hp, this]
    · have : (m * t) ^ 2 - 1 ≠ 0 := by intro h; apply hp; nlinarith
      field_simp
  · have := ((hu.comp t hmt).div_const m)
    refine this.congr_deriv ?_
    unfold qm qP; field_simp

/-- `D = (m² − r²) E`, `E = c²t²(t² − 1/r² − 1/m²) + χ/(m²r²)`. -/
theorem Dmr_eq {c χ m r : ℝ} (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    Dmr c χ m r t = (m ^ 2 - r ^ 2) * (c ^ 2 * t ^ 2 * (t ^ 2 - 1 / r ^ 2 - 1 / m ^ 2) + χ / (m ^ 2 * r ^ 2)) := by
  unfold Dmr pm qm; field_simp; ring

/-- **The non-stationary pair bound.** -/
theorem pair_le {c χ GM Ξ m₁ m₂ s T : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hm₂ : 0 < m₂) (h12 : m₂ < m₁) (hs : 2 ≤ m₂ * s) (hsT : s ≤ T) (hT : m₁ * T ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χ) ψ u ξ ≤ GM) :
    |∫ t in s..T, ψ (m₁ * t) * ψ (m₂ * t)|
      ≤ 4 * GM * √(2 * c / (√3 * √(c ^ 2 - χ))) / (c ^ 2 * s ^ 2 * (m₁ * m₂ * (m₁ - m₂))) := by
  have hm₁ : 0 < m₁ := hm₂.trans h12
  have hs0 : 0 < s := by by_contra h; push Not at h; nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  set κ := 2 * c / (√3 * √(c ^ 2 - χ)) with hκ
  have hκ0 : 0 ≤ √κ := sqrt_nonneg _
  have hGM : 0 ≤ GM := by
    have h2 : (2 : ℝ) ∈ Icc 2 Ξ := ⟨le_rfl, by nlinarith [hsT]⟩
    have ha := aP_pos (by norm_num : (1 : ℝ) < 2) hc2 hχ
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
    linarith [hG 2 h2, abs_nonneg (ψ 2 * u 2)]
  have in2 : ∀ τ ∈ Icc s T, m₂ * τ ∈ Icc 2 Ξ := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2, hτ.1]⟩
  have in1 : ∀ τ ∈ Icc s T, m₁ * τ ∈ Icc 2 Ξ := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  -- the scaled systems
  have sys : ∀ k : ℝ, 0 < k → (∀ τ ∈ Icc s T, k * τ ∈ Icc 2 Ξ) → ∀ τ ∈ Icc s T,
      HasDerivAt (fun t => ψ (k * t)) ((u (k * τ) / k) / pm k τ) τ ∧
      HasDerivAt (fun t => u (k * t) / k) (-(qm c χ k τ * ψ (k * τ))) τ := fun k hk hin τ hτ =>
    scale_system hk (hψ _ (hin τ hτ)) (hu _ (hin τ hτ))
  -- D > 0 with E ≥ c²τ⁴/2
  have hE : ∀ τ ∈ Icc s T, c ^ 2 * τ ^ 4 / 2 ≤
      c ^ 2 * τ ^ 2 * (τ ^ 2 - 1 / m₂ ^ 2 - 1 / m₁ ^ 2) + χ / (m₁ ^ 2 * m₂ ^ 2) := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h2 : 2 ≤ m₂ * τ := le_trans hs (by nlinarith [hτ.1])
    have e2 : 1 / m₂ ^ 2 ≤ τ ^ 2 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have e1 : 1 / m₁ ^ 2 ≤ 1 / m₂ ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have : 0 ≤ χ / (m₁ ^ 2 * m₂ ^ 2) := by positivity
    have : c ^ 2 * τ ^ 2 * (τ ^ 2 / 2) ≤ c ^ 2 * τ ^ 2 * (τ ^ 2 - 1 / m₂ ^ 2 - 1 / m₁ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hDpos : ∀ τ ∈ Icc s T, 0 < Dmr c χ m₁ m₂ τ := fun τ hτ => by
    rw [Dmr_eq hm₁.ne' hm₂.ne']
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h0 : 0 < c ^ 2 * τ ^ 4 / 2 := by positivity
    have h1 : 0 < m₁ ^ 2 - m₂ ^ 2 := by nlinarith
    exact mul_pos h1 (lt_of_lt_of_le h0 (hE τ hτ))
  -- the cross sups
  have hZ : ∀ τ ∈ Icc s T, |ψ (m₁ * τ) * (u (m₂ * τ) / m₂)| ≤ GM * √κ / m₁ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.cross_env hc hχ0 hχ (in1 τ hτ).1 (in2 τ hτ).1
      (hG _ (in1 τ hτ)) (hG _ (in2 τ hτ))
    rw [show ψ (m₁ * τ) * (u (m₂ * τ) / m₂) = ψ (m₁ * τ) * u (m₂ * τ) / m₂ by ring, abs_div,
      abs_of_pos hm₂, div_le_iff₀ hm₂]
    calc |ψ (m₁ * τ) * u (m₂ * τ)| ≤ GM * √κ * (m₂ * τ / (m₁ * τ)) := h
      _ = GM * √κ / m₁ * m₂ := by field_simp
  have hV : ∀ τ ∈ Icc s T, |u (m₁ * τ) / m₁ * ψ (m₂ * τ)| ≤ GM * √κ / m₂ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.cross_env hc hχ0 hχ (in2 τ hτ).1 (in1 τ hτ).1
      (hG _ (in2 τ hτ)) (hG _ (in1 τ hτ))
    rw [show u (m₁ * τ) / m₁ * ψ (m₂ * τ) = ψ (m₂ * τ) * u (m₁ * τ) / m₁ by ring, abs_div,
      abs_of_pos hm₁, div_le_iff₀ hm₁]
    calc |ψ (m₂ * τ) * u (m₁ * τ)| ≤ GM * √κ * (m₁ * τ / (m₂ * τ)) := h
      _ = GM * √κ / m₂ * m₁ := by field_simp
  have key := prolate_cross_le (c := c) (χ := χ) (m := m₁) (r := m₂)
    (f₁ := fun t => ψ (m₁ * t)) (u₁ := fun t => u (m₁ * t) / m₁)
    (f₂ := fun t => ψ (m₂ * t)) (u₂ := fun t => u (m₂ * t) / m₂) hsT hm₂ h12 (by linarith) hχ hDpos
    (fun τ hτ => (sys m₁ hm₁ in1 τ hτ).1) (fun τ hτ => (sys m₁ hm₁ in1 τ hτ).2)
    (fun τ hτ => (sys m₂ hm₂ in2 τ hτ).1) (fun τ hτ => (sys m₂ hm₂ in2 τ hτ).2) hZ hV
  -- closed form
  have hmemS : s ∈ Icc s T := left_mem_Icc.mpr hsT
  have hDs : (m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * s ^ 4 / 2) ≤ Dmr c χ m₁ m₂ s := by
    rw [Dmr_eq hm₁.ne' hm₂.ne']
    exact mul_le_mul_of_nonneg_left (hE s hmemS) (by nlinarith)
  have hp1 : pm m₁ s ≤ s ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hp2 : pm m₂ s ≤ s ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hnum : 2 * (pm m₁ s * (GM * √κ / m₁) + pm m₂ s * (GM * √κ / m₂))
      ≤ 2 * (s ^ 2 * (GM * √κ / m₁) + s ^ 2 * (GM * √κ / m₂)) := by
    have : 0 ≤ GM * √κ / m₁ := by positivity
    have : 0 ≤ GM * √κ / m₂ := by positivity
    nlinarith
  have hDpos' : 0 < (m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * s ^ 4 / 2) := by
    have : 0 < m₁ ^ 2 - m₂ ^ 2 := by nlinarith
    positivity
  calc |∫ t in s..T, ψ (m₁ * t) * ψ (m₂ * t)|
      ≤ 2 * (pm m₁ s * (GM * √κ / m₁) + pm m₂ s * (GM * √κ / m₂)) / Dmr c χ m₁ m₂ s := key
    _ ≤ 2 * (s ^ 2 * (GM * √κ / m₁) + s ^ 2 * (GM * √κ / m₂)) / ((m₁ ^ 2 - m₂ ^ 2) * (c ^ 2 * s ^ 4 / 2)) := by
        apply div_le_div₀ (by positivity) hnum hDpos' hDs
    _ = 4 * GM * √κ / (c ^ 2 * s ^ 2 * (m₁ * m₂ * (m₁ - m₂))) := by
        have : m₁ - m₂ ≠ 0 := by linarith
        have : m₁ ^ 2 - m₂ ^ 2 ≠ 0 := by nlinarith
        have : -m₂ ^ 2 + m₁ ^ 2 ≠ 0 := by nlinarith
        field_simp; ring

end Cvs.L2a.NonstationaryCrossPairClosed
