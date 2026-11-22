import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
# Pointwise envelopes from the Liouville–Green energy

`ψ² ≤ G/a` and `u² ≤ aG`, and for the prolate `(√3/2)√(c²−χ) ξ² ≤ a(ξ) ≤ cξ²` once `ξ ≥ 2`, so a product of a value
at `ξ₁` and a flux at `ξ₂`, both with energy at most `G_M`, is at most `G_M √κ ξ₂/ξ₁`, `κ = 2c/(√3 √(c²−χ))`.
-/

namespace Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes

open Real Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `ψ² ≤ G/a`. -/
theorem sq_le_energy_div {a ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) : ψ t ^ 2 ≤ energy a ψ u t / a t := by
  unfold energy; rw [le_div_iff₀ ha]
  have : 0 ≤ u t ^ 2 / a t * a t := by positivity
  nlinarith [this]

/-- `u² ≤ a G`. -/
theorem flux_sq_le {a ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) : u t ^ 2 ≤ a t * energy a ψ u t := by
  unfold energy
  have e : a t * (a t * ψ t ^ 2 + u t ^ 2 / a t) = a t ^ 2 * ψ t ^ 2 + u t ^ 2 := by field_simp
  rw [e]; nlinarith [sq_nonneg (a t * ψ t)]

/-- `a(ξ) ≤ c ξ²` for `ξ ≥ 1`, `0 ≤ χ`, `0 < c`. -/
theorem aP_le {c χ ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hξ : 1 ≤ ξ) : aP c χ ξ ≤ c * ξ ^ 2 := by
  unfold aP pP qP
  rw [sqrt_le_left (by positivity)]
  have : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg this hχ, sq_nonneg (c * ξ ^ 2), mul_nonneg (sq_nonneg c) (sq_nonneg ξ)]

/-- `(√3/2) √(c²−χ) ξ² ≤ a(ξ)` for `ξ ≥ 2`, `0 ≤ χ < c²`. -/
theorem le_aP {c χ ξ : ℝ} (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hξ : 2 ≤ ξ) :
    √3 / 2 * √(c ^ 2 - χ) * ξ ^ 2 ≤ aP c χ ξ := by
  unfold aP pP qP
  have hd : 0 ≤ c ^ 2 - χ := by linarith
  rw [show √3 / 2 * √(c ^ 2 - χ) * ξ ^ 2 = √(3 / 4 * (c ^ 2 - χ) * ξ ^ 4) by
    rw [sqrt_mul (by positivity), sqrt_mul (by norm_num), show ξ ^ 4 = (ξ ^ 2) ^ 2 by ring,
      sqrt_sq (by positivity), show (3 : ℝ) / 4 = 3 / 2 ^ 2 by norm_num, sqrt_div (by norm_num),
      sqrt_sq (by norm_num)]]
  apply sqrt_le_sqrt
  have h1 : 3 / 4 * ξ ^ 2 ≤ ξ ^ 2 - 1 := by nlinarith
  have h2 : (c ^ 2 - χ) * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
  have : 0 ≤ (c ^ 2 - χ) * ξ ^ 2 := by positivity
  calc 3 / 4 * (c ^ 2 - χ) * ξ ^ 4 = (3 / 4 * ξ ^ 2) * ((c ^ 2 - χ) * ξ ^ 2) := by ring
    _ ≤ (ξ ^ 2 - 1) * (c ^ 2 * ξ ^ 2 - χ) := mul_le_mul h1 h2 this (by nlinarith)

/-- **The cross envelope**: for `ξ₁, ξ₂ ≥ 2` with energies at most `G_M`,
`|ψ(ξ₁) u(ξ₂)| ≤ G_M √κ ξ₂/ξ₁`, `κ = 2c/(√3 √(c²−χ))`. -/
theorem cross_env {c χ GM ξ₁ ξ₂ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (h₁ : 2 ≤ ξ₁) (h₂ : 2 ≤ ξ₂) (hG₁ : energy (aP c χ) ψ u ξ₁ ≤ GM) (hG₂ : energy (aP c χ) ψ u ξ₂ ≤ GM) :
    |ψ ξ₁ * u ξ₂| ≤ GM * √(2 * c / (√3 * √(c ^ 2 - χ))) * (ξ₂ / ξ₁) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha₁ := aP_pos (by linarith : (1:ℝ) < ξ₁) hc2 hχ
  have ha₂ := aP_pos (by linarith : (1:ℝ) < ξ₂) hc2 hχ
  have hd : 0 < c ^ 2 - χ := by linarith
  have hs3 : 0 < √3 := by positivity
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hψ := sq_le_energy_div (u := u) (ψ := ψ) ha₁
  have hu := flux_sq_le (u := u) (ψ := ψ) ha₂
  have hGM : 0 ≤ GM := le_trans (by
    have := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.two_mul_abs_le_energy (ψ := ψ) (u := u) ha₁; linarith [abs_nonneg (ψ ξ₁ * u ξ₁)]) hG₁
  -- (ψ u)² ≤ G_M² a₂/a₁ ≤ G_M² κ ξ₂²/ξ₁²
  have hprod : (ψ ξ₁ * u ξ₂) ^ 2 ≤ GM ^ 2 * (aP c χ ξ₂ / aP c χ ξ₁) := by
    rw [mul_pow]
    have e1 : ψ ξ₁ ^ 2 ≤ GM / aP c χ ξ₁ := hψ.trans (div_le_div_of_nonneg_right hG₁ ha₁.le)
    have e2 : u ξ₂ ^ 2 ≤ aP c χ ξ₂ * GM := hu.trans (mul_le_mul_of_nonneg_left hG₂ ha₂.le)
    calc ψ ξ₁ ^ 2 * u ξ₂ ^ 2 ≤ GM / aP c χ ξ₁ * (aP c χ ξ₂ * GM) :=
          mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
      _ = GM ^ 2 * (aP c χ ξ₂ / aP c χ ξ₁) := by field_simp
  have hratio : aP c χ ξ₂ / aP c χ ξ₁ ≤ 2 * c / (√3 * √(c ^ 2 - χ)) * (ξ₂ / ξ₁) ^ 2 := by
    have up := aP_le hc hχ0 (by linarith : (1:ℝ) ≤ ξ₂)
    have lo := le_aP hχ0 hχ h₁
    rw [div_le_iff₀ ha₁]
    calc aP c χ ξ₂ ≤ c * ξ₂ ^ 2 := up
      _ = 2 * c / (√3 * √(c ^ 2 - χ)) * (ξ₂ / ξ₁) ^ 2 * (√3 / 2 * √(c ^ 2 - χ) * ξ₁ ^ 2) := by
          field_simp
      _ ≤ 2 * c / (√3 * √(c ^ 2 - χ)) * (ξ₂ / ξ₁) ^ 2 * aP c χ ξ₁ :=
          mul_le_mul_of_nonneg_left lo (by positivity)
  have hbound : (ψ ξ₁ * u ξ₂) ^ 2 ≤ (GM * √(2 * c / (√3 * √(c ^ 2 - χ))) * (ξ₂ / ξ₁)) ^ 2 := by
    have hK : 0 ≤ 2 * c / (√3 * √(c ^ 2 - χ)) := by positivity
    rw [show (GM * √(2 * c / (√3 * √(c ^ 2 - χ))) * (ξ₂ / ξ₁)) ^ 2
        = GM ^ 2 * (2 * c / (√3 * √(c ^ 2 - χ))) * (ξ₂ / ξ₁) ^ 2 by
      rw [mul_pow, mul_pow, sq_sqrt hK]]
    calc (ψ ξ₁ * u ξ₂) ^ 2 ≤ GM ^ 2 * (aP c χ ξ₂ / aP c χ ξ₁) := hprod
      _ ≤ GM ^ 2 * (2 * c / (√3 * √(c ^ 2 - χ)) * (ξ₂ / ξ₁) ^ 2) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = _ := by ring
  have hR : 0 ≤ GM * √(2 * c / (√3 * √(c ^ 2 - χ))) * (ξ₂ / ξ₁) := by
    have : 0 < ξ₁ := by linarith
    have : 0 < ξ₂ := by linarith
    positivity
  exact abs_le_of_sq_le_sq' hbound hR |> fun h => abs_le.mpr ⟨h.1, h.2⟩

end Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
