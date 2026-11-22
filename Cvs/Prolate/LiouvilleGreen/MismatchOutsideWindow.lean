import Mathlib
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow
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
# The rate mismatch outside the window, in explicit form

Below the stationary point, on `[p, t]` with `t² ≤ θ*² − Δ`, the rate of a prolate rung exceeds the profile's
`cm′` by at least `c(m′² − 1)Δ√(p² − 1)/(2p(θ*² − 1)) − p²/(p² − 1)^{3/2}`, and above it, on `[t, q]` with
`t² ≥ θ*² + Δ`, the profile's rate exceeds the rung's by at least `c(m′² − 1)Δ/(2m′(q² − 1)) − t₀²/(t₀² − 1)^{3/2}`
for any `t₀ ≤ t`: the `λδ` of Cvs.Upstream.SecondDerivativeWindowTest with every quantity a closed form in `c`, `χ`, `m′`, `Δ` and the window's ends.
-/

namespace Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferRateFrequency Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch

/-- `t/√(t² − 1)` decreases on `(1, ∞)`. -/
theorem div_sqrt_antitone {p t : ℝ} (hp : 1 < p) (hpt : p ≤ t) : t / √(t ^ 2 - 1) ≤ p / √(p ^ 2 - 1) := by
  have h1 : (0 : ℝ) < p ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hs : (t / √(t ^ 2 - 1)) ^ 2 ≤ (p / √(p ^ 2 - 1)) ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt h2.le, sq_sqrt h1.le, div_le_div_iff₀ h2 h1]
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hs

/-- `t/(t² − 1)` decreases on `(1, ∞)`. -/
theorem div_sub_antitone {p t : ℝ} (hp : 1 < p) (hpt : p ≤ t) : t / (t ^ 2 - 1) ≤ p / (p ^ 2 - 1) := by
  have h1 : (0 : ℝ) < p ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpt) (by nlinarith : (0 : ℝ) ≤ p * t + 1)]

/-- **The rate correction beyond `p`**: `|w|(a/p)/2 ≤ (p/√(p² − 1))·(p/(p² − 1))` for `t ≥ p > 1`. -/
theorem correction_le {c χ p t : ℝ} (hp : 1 < p) (hpt : p ≤ t) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    |wP c χ t| * (aP c χ t / pP t) / 2 ≤ p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1)) := by
  have ht : 1 < t := lt_of_lt_of_le hp hpt
  have hc2 : 0 < c ^ 2 := by positivity
  have hw0 : 0 < wP c χ t := wP_pos ht hc2 hχc
  have hwle : wP c χ t ≤ 2 * t / (c * pP t) := wP_le_far ht hc hχ0 hχc
  have hpP : pP t = t ^ 2 - 1 := rfl
  rw [hpP] at hwle
  obtain ⟨-, hfh⟩ := freq_bounds (χ := χ) ht hc hχ0 hχc
  have hfreq : 0 ≤ aP c χ t / pP t := (div_pos (aP_pos ht hc2 hχc) (pP_pos ht)).le
  have h2 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  rw [abs_of_pos hw0]
  calc wP c χ t * (aP c χ t / pP t) / 2 ≤ 2 * t / (c * (t ^ 2 - 1)) * (c * t / √(t ^ 2 - 1)) / 2 := by
        gcongr
    _ = t / √(t ^ 2 - 1) * (t / (t ^ 2 - 1)) := by field_simp
    _ ≤ p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1)) :=
        mul_le_mul (div_sqrt_antitone hp hpt) (div_sub_antitone hp hpt) (by positivity) (by positivity)

/-- **Below the window, explicitly**: on `[p, t]` with `t² ≤ θ*² − Δ`,
`rate − cm′ ≥ c(m′² − 1)Δ√(p² − 1)/(2p(θ*² − 1)) − (p/√(p² − 1))(p/(p² − 1))`. -/
theorem rate_sub_profile_ge_explicit {c χ p t Δ : ℝ} {m' : ℕ} {ψ u : ℝ → ℝ} (hp : 1 < p) (hpt : p ≤ t)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 2 ≤ m') (hΔ : 0 ≤ Δ)
    (hbelow : t ^ 2 ≤ statSq c χ m' - Δ) (hE : 0 < energy (aP c χ) ψ u t) :
    c * ((m' : ℝ) ^ 2 - 1) * Δ * √(p ^ 2 - 1) / (2 * p * (statSq c χ m' - 1))
        - p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))
      ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t - c * m' := by
  have ht : 1 < t := lt_of_lt_of_le hp hpt
  have hm : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
  have hm2 : (0 : ℝ) < (m' : ℝ) ^ 2 - 1 := by nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h2 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have h1 : (0 : ℝ) < p ^ 2 - 1 := by nlinarith
  have hstat : 0 < statSq c χ m' - 1 := by
    unfold statSq
    have : 0 < (c ^ 2 - χ) / (c ^ 2 * ((m' : ℝ) ^ 2 - 1)) := div_pos (by linarith) (by positivity)
    linarith
  have hfreq : 0 < aP c χ t / pP t := div_pos (aP_pos ht hc2 hχc) (pP_pos ht)
  obtain ⟨-, hfh⟩ := freq_bounds (χ := χ) ht hc hχ0 hχc
  -- below the stationary point the frequency exceeds `cm′`, so `a/p + cm′ ≤ 2 a/p ≤ 2cp/√(p² − 1)`
  have hge : c * m' ≤ aP c χ t / pP t := by
    have key := freq_sq_sub_profile (χ := χ) ht hc hχ0 hχc hm'
    have hnn : 0 ≤ c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (statSq c χ m' - t ^ 2) / (t ^ 2 - 1) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) h2.le
    have hsq : (c * m') ^ 2 ≤ (aP c χ t / pP t) ^ 2 := by linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hfreq.le hsq
  have hsum : aP c χ t / pP t + c * m' ≤ 2 * (c * p / √(p ^ 2 - 1)) := by
    have := div_sqrt_antitone hp hpt
    have h3 : c * t / √(t ^ 2 - 1) ≤ c * p / √(p ^ 2 - 1) := by
      rw [mul_div_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_left this hc.le
    linarith
  have hden : (t ^ 2 - 1) * (aP c χ t / pP t + c * m') ≤ (statSq c χ m' - 1) * (2 * (c * p / √(p ^ 2 - 1))) := by
    apply mul_le_mul _ hsum (by positivity) hstat.le
    linarith
  have hmain := rate_sub_profile_ge (χ := χ) (ψ := ψ) (u := u) ht hc hχ0 hχc hm' hbelow hE
  have hcorr := correction_le (χ := χ) hp hpt hc hχ0 hχc
  have hden0 : 0 < (t ^ 2 - 1) * (aP c χ t / pP t + c * m') := by positivity
  have hfrac : c * ((m' : ℝ) ^ 2 - 1) * Δ * √(p ^ 2 - 1) / (2 * p * (statSq c χ m' - 1))
      ≤ c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m')) := by
    have hsp : 0 < √(p ^ 2 - 1) := Real.sqrt_pos.mpr h1
    rw [div_le_div_iff₀ (by positivity) hden0]
    calc c * ((m' : ℝ) ^ 2 - 1) * Δ * √(p ^ 2 - 1) * ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
        ≤ c * ((m' : ℝ) ^ 2 - 1) * Δ * √(p ^ 2 - 1) * ((statSq c χ m' - 1) * (2 * (c * p / √(p ^ 2 - 1)))) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ = c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ * (2 * p * (statSq c χ m' - 1)) := by
          field_simp
  linarith

end Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow
