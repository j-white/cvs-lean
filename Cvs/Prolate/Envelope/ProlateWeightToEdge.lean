import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
# The prolate weight is `ξ√(ξ²−1)` up to `[√(c²−χ), c]`, all the way to the edge

`√(c²−χ) ξ√(ξ²−1) ≤ a(ξ) ≤ c ξ√(ξ²−1)` for `ξ ≥ 1`, `0 ≤ χ < c²`, so a value at `ξ₁` times a flux at `ξ₂`, both with
energy at most `G`, is at most `G √(κ₀ ξ₂√(ξ₂²−1)/(ξ₁√(ξ₁²−1)))`, `κ₀ = c/√(c²−χ)`, for every `ξ₁, ξ₂ > 1`.
-/

namespace Cvs.Prolate.Envelope.ProlateWeightToEdge

open Real Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- The edge weight `ξ√(ξ²−1)`. -/
noncomputable def ew (ξ : ℝ) : ℝ := ξ * √(ξ ^ 2 - 1)

theorem aP_le' {c χ ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hξ : 1 ≤ ξ) : aP c χ ξ ≤ c * ew ξ := by
  unfold aP pP qP ew
  have hp : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  rw [show c * (ξ * √(ξ ^ 2 - 1)) = √((ξ ^ 2 - 1) * (c ^ 2 * ξ ^ 2)) by
    rw [sqrt_mul hp, show c ^ 2 * ξ ^ 2 = (c * ξ) ^ 2 by ring, sqrt_sq (by positivity)]; ring]
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (by linarith) hp

theorem le_aP' {c χ ξ : ℝ} (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hξ : 1 ≤ ξ) :
    √(c ^ 2 - χ) * ew ξ ≤ aP c χ ξ := by
  unfold aP pP qP ew
  have hp : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  have hd : 0 ≤ c ^ 2 - χ := by linarith
  rw [show √(c ^ 2 - χ) * (ξ * √(ξ ^ 2 - 1)) = √((ξ ^ 2 - 1) * ((c ^ 2 - χ) * ξ ^ 2)) by
    rw [sqrt_mul hp, sqrt_mul hd, sqrt_sq (by linarith)]; ring]
  apply sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ hp
  nlinarith [mul_nonneg hχ0 hp]

/-- **The cross envelope, up to the edge**: for `ξ₁, ξ₂ > 1` with energies at most `G`,
`|ψ(ξ₁) u(ξ₂)| ≤ G √(κ₀ ew(ξ₂)/ew(ξ₁))`, `κ₀ = c/√(c²−χ)`. -/
theorem cross_env' {c χ G ξ₁ ξ₂ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (h₁ : 1 < ξ₁) (h₂ : 1 < ξ₂) (hG₁ : energy (aP c χ) ψ u ξ₁ ≤ G) (hG₂ : energy (aP c χ) ψ u ξ₂ ≤ G) :
    |ψ ξ₁ * u ξ₂| ≤ G * √(c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha₁ := aP_pos h₁ hc2 hχ
  have ha₂ := aP_pos h₂ hc2 hχ
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hew : ∀ ξ : ℝ, 1 < ξ → 0 < ew ξ := fun ξ h => by
    unfold ew; have : 0 < ξ ^ 2 - 1 := by nlinarith
    have := sqrt_pos.mpr this; positivity
  have hψ := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (u := u) (ψ := ψ) ha₁
  have hu := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.flux_sq_le (u := u) (ψ := ψ) ha₂
  have hG : 0 ≤ G := le_trans (by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha₁; linarith [abs_nonneg (ψ ξ₁ * u ξ₁)]) hG₁
  have hprod : (ψ ξ₁ * u ξ₂) ^ 2 ≤ G ^ 2 * (aP c χ ξ₂ / aP c χ ξ₁) := by
    rw [mul_pow]
    have e1 : ψ ξ₁ ^ 2 ≤ G / aP c χ ξ₁ := hψ.trans (div_le_div_of_nonneg_right hG₁ ha₁.le)
    have e2 : u ξ₂ ^ 2 ≤ aP c χ ξ₂ * G := hu.trans (mul_le_mul_of_nonneg_left hG₂ ha₂.le)
    calc ψ ξ₁ ^ 2 * u ξ₂ ^ 2 ≤ G / aP c χ ξ₁ * (aP c χ ξ₂ * G) :=
          mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
      _ = G ^ 2 * (aP c χ ξ₂ / aP c χ ξ₁) := by field_simp
  have hratio : aP c χ ξ₂ / aP c χ ξ₁ ≤ c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁) := by
    have up := aP_le' hc hχ0 h₂.le
    have lo := le_aP' hχ0 hχ h₁.le
    have he1 := hew ξ₁ h₁
    rw [div_le_iff₀ ha₁]
    calc aP c χ ξ₂ ≤ c * ew ξ₂ := up
      _ = c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁) * (√(c ^ 2 - χ) * ew ξ₁) := by field_simp
      _ ≤ c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁) * aP c χ ξ₁ :=
          mul_le_mul_of_nonneg_left lo (by have := hew ξ₂ h₂; positivity)
  have hK : 0 ≤ c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁) := by
    have := hew ξ₁ h₁; have := hew ξ₂ h₂; positivity
  have hbound : (ψ ξ₁ * u ξ₂) ^ 2 ≤ (G * √(c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁))) ^ 2 := by
    rw [show (G * √(c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁))) ^ 2
        = G ^ 2 * (c / √(c ^ 2 - χ) * (ew ξ₂ / ew ξ₁)) by rw [mul_pow, sq_sqrt hK]]
    exact hprod.trans (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
  exact abs_le_of_sq_le_sq' hbound (by positivity) |> fun h => abs_le.mpr ⟨h.1, h.2⟩

end Cvs.Prolate.Envelope.ProlateWeightToEdge
