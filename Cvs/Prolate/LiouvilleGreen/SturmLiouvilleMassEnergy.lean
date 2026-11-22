import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The L² mass of a Sturm–Liouville solution is its energy over `2a`

For `ψ' = u/p`, `u' = −qψ`, `a² = pq`, `ψ² = G/(2a) − (ψu/q)'/2 − ψu q'/(2q²)`, so
`∫ψ² = ∫(G/(2a) − ψu q'/(2q²)) − [ψu/q]/2`, and `|∫ψ² − ∫G/(2a)|` is at most `G/(4q)` at both ends plus
`∫ G|q'|/(4q²)`: the averaging `⟨ψ²⟩ = G/(2a)` of WKB, with its error.
-/

namespace Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

variable {ψ u p q a q' : ℝ → ℝ}

/-- The pointwise identity `ψ² = G/(2a) − ψu q'/(2q²) − D/2`, `D = (ψu/q)'` written out. -/
theorem sq_eq {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hq : q t ≠ 0) (hapq : a t ^ 2 = p t * q t) :
    ψ t ^ 2 = energy a ψ u t / (2 * a t) - ψ t * u t * q' t / (2 * q t ^ 2)
      - (((u t / p t) * u t + ψ t * -(q t * ψ t)) * q t - ψ t * u t * q' t) / q t ^ 2 / 2 := by
  unfold energy
  have hp' : p t = a t ^ 2 / q t := by rw [hapq]; field_simp
  rw [hp']
  field_simp
  ring

/-- **The L² identity.** On `[t₀, t₁]`, with `q` differentiable with continuous derivative `q'`,
`∫ψ² = ∫(G/(2a) − ψu q'/(2q²)) − (ψu/q)(t₁)/2 + (ψu/q)(t₀)/2`. -/
theorem integral_sq_eq {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0) (hq : ∀ t ∈ Icc t₀ t₁, q t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (hqd : ∀ t ∈ Icc t₀ t₁, HasDerivAt q (q' t) t) (hq'c : ContinuousOn q' (Icc t₀ t₁))
    (hac : ContinuousOn a (Icc t₀ t₁)) (hpc : ContinuousOn p (Icc t₀ t₁)) :
    ∫ t in t₀..t₁, ψ t ^ 2
      = (∫ t in t₀..t₁, (energy a ψ u t / (2 * a t) - ψ t * u t * q' t / (2 * q t ^ 2)))
        - ψ t₁ * u t₁ / q t₁ / 2 + ψ t₀ * u t₀ / q t₀ / 2 := by
  have hI : uIcc t₀ t₁ = Icc t₀ t₁ := uIcc_of_le hle
  have cont : ∀ f : ℝ → ℝ, (∀ t ∈ Icc t₀ t₁, DifferentiableAt ℝ f t) → ContinuousOn f (Icc t₀ t₁) :=
    fun f hf t ht => (hf t ht).continuousAt.continuousWithinAt
  have hψc := cont ψ fun t ht => (hψ t ht).differentiableAt
  have huc := cont u fun t ht => (hu t ht).differentiableAt
  have hqc := cont q fun t ht => (hqd t ht).differentiableAt
  -- the derivative of ψu/q
  set D : ℝ → ℝ := fun t => (((u t / p t) * u t + ψ t * -(q t * ψ t)) * q t - ψ t * u t * q' t) / q t ^ 2
  have hD : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => ψ s * u s / q s) (D t) t := fun t ht =>
    ((hψ t ht).fun_mul (hu t ht)).fun_div (hqd t ht) (hq t ht)
  have hDc : ContinuousOn D (Icc t₀ t₁) := by
    refine ContinuousOn.div ?_ (hqc.pow 2) (fun t ht => pow_ne_zero 2 (hq t ht))
    exact ((((huc.div hpc hp).mul huc).add (hψc.mul (hqc.mul hψc).neg)).mul hqc).sub
      ((hψc.mul huc).mul hq'c)
  have hFTC := integral_eq_sub_of_hasDerivAt (fun t ht => hD t (hI ▸ ht))
    (hDc.intervalIntegrable_of_Icc hle)
  have hGc : ContinuousOn (fun t => energy a ψ u t / (2 * a t) - ψ t * u t * q' t / (2 * q t ^ 2))
      (Icc t₀ t₁) := by
    unfold energy
    refine ContinuousOn.sub ?_ ?_
    · exact ((hac.mul (hψc.pow 2)).add ((huc.pow 2).div hac fun t ht => (ha t ht).ne')).div
        (continuousOn_const.mul hac) fun t ht => mul_ne_zero two_ne_zero (ha t ht).ne'
    · exact ((hψc.mul huc).mul hq'c).div (continuousOn_const.mul (hqc.pow 2))
        fun t ht => mul_ne_zero two_ne_zero (pow_ne_zero 2 (hq t ht))
  have hpt : ∀ t ∈ Icc t₀ t₁, ψ t ^ 2
      = (energy a ψ u t / (2 * a t) - ψ t * u t * q' t / (2 * q t ^ 2)) - D t / 2 := by
    intro t ht
    have := sq_eq (ψ := ψ) (u := u) (q' := q') (ha t ht) (hp t ht) (hq t ht) (hapq t ht)
    exact this
  rw [intervalIntegral.integral_congr (g := fun t =>
      (energy a ψ u t / (2 * a t) - ψ t * u t * q' t / (2 * q t ^ 2)) - D t / 2)
      (fun t ht => hpt t (hI ▸ ht)),
    intervalIntegral.integral_sub (hGc.intervalIntegrable_of_Icc hle)
      ((hDc.div_const 2).intervalIntegrable_of_Icc hle),
    intervalIntegral.integral_div, hFTC]
  ring

end Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy
