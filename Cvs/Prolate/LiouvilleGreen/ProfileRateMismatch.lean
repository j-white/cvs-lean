import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferRateFrequency
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
# The mismatch away from the stationary point

Below the stationary point `θ*` of Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint by `Δ` in the square, `t² ≤ θ*² − Δ`, the frequency exceeds the profile's
by `(a/p)(t) − cm′ ≥ c²(m′² − 1)Δ/((t² − 1)((a/p)(t) + cm′))`, and above it by `Δ` the profile's exceeds the
frequency by the same amount; subtracting the rate correction `|w|(a/p)/2` of Cvs.Prolate.LiouvilleGreen.PruferRateFrequency gives the same for the Prüfer
rate. These are the `λδ` bounds outside the window that the test of Cvs.Upstream.SecondDerivativeWindowTest needs, with the window's width as `Δ`.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferRateFrequency Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint

/-- **The mismatch below the stationary point**: for `t² ≤ θ*² − Δ`,
`(a/p)(t) − cm′ ≥ c²(m′² − 1)Δ/((t² − 1)((a/p)(t) + cm′))`. -/
theorem freq_sub_profile_ge {c χ t Δ : ℝ} {m' : ℕ} (ht : 1 < t) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hm' : 2 ≤ m') (hbelow : t ^ 2 ≤ statSq c χ m' - Δ) :
    c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
      ≤ aP c χ t / pP t - c * m' := by
  have hm : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
  have h1 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < (m' : ℝ) ^ 2 - 1 := by nlinarith
  have hfreq : 0 < aP c χ t / pP t := div_pos (aP_pos ht (by positivity) hχc) (pP_pos ht)
  have hsum : 0 < aP c χ t / pP t + c * m' := by positivity
  have key := freq_sq_sub_profile (χ := χ) ht hc hχ0 hχc hm'
  -- `(a/p)² − (cm′)² = (a/p − cm′)(a/p + cm′)`
  have hfac : (aP c χ t / pP t) ^ 2 - (c * m') ^ 2
      = (aP c χ t / pP t - c * m') * (aP c χ t / pP t + c * m') := by ring
  rw [hfac] at key
  have hΔle : Δ ≤ statSq c χ m' - t ^ 2 := by linarith
  rw [div_le_iff₀ (mul_pos h1 hsum)]
  calc c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ ≤ c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (statSq c χ m' - t ^ 2) :=
        mul_le_mul_of_nonneg_left hΔle (by positivity)
    _ = (aP c χ t / pP t - c * m') * (aP c χ t / pP t + c * m') * (t ^ 2 - 1) := by
        rw [key]; field_simp
    _ = (aP c χ t / pP t - c * m') * ((t ^ 2 - 1) * (aP c χ t / pP t + c * m')) := by ring

/-- **The mismatch above the stationary point**: for `t² ≥ θ*² + Δ`,
`cm′ − (a/p)(t) ≥ c²(m′² − 1)Δ/((t² − 1)((a/p)(t) + cm′))`. -/
theorem profile_sub_freq_ge {c χ t Δ : ℝ} {m' : ℕ} (ht : 1 < t) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hm' : 2 ≤ m') (habove : statSq c χ m' + Δ ≤ t ^ 2) :
    c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
      ≤ c * m' - aP c χ t / pP t := by
  have hm : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
  have h1 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < (m' : ℝ) ^ 2 - 1 := by nlinarith
  have hfreq : 0 < aP c χ t / pP t := div_pos (aP_pos ht (by positivity) hχc) (pP_pos ht)
  have hsum : 0 < aP c χ t / pP t + c * m' := by positivity
  have key := freq_sq_sub_profile (χ := χ) ht hc hχ0 hχc hm'
  have hfac : (c * m') ^ 2 - (aP c χ t / pP t) ^ 2
      = (c * m' - aP c χ t / pP t) * (aP c χ t / pP t + c * m') := by ring
  have key' : (c * m') ^ 2 - (aP c χ t / pP t) ^ 2
      = c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (t ^ 2 - statSq c χ m') / (t ^ 2 - 1) := by
    rw [← neg_sub, key]; field_simp; ring
  rw [hfac] at key'
  have hΔle : Δ ≤ t ^ 2 - statSq c χ m' := by linarith
  rw [div_le_iff₀ (mul_pos h1 hsum)]
  calc c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ ≤ c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (t ^ 2 - statSq c χ m') :=
        mul_le_mul_of_nonneg_left hΔle (by positivity)
    _ = (c * m' - aP c χ t / pP t) * (aP c χ t / pP t + c * m') * (t ^ 2 - 1) := by
        rw [key']; field_simp
    _ = (c * m' - aP c χ t / pP t) * ((t ^ 2 - 1) * (aP c χ t / pP t + c * m')) := by ring

/-- **The rate mismatch below the stationary point**, with the correction of Cvs.Prolate.LiouvilleGreen.PruferRateFrequency subtracted. -/
theorem rate_sub_profile_ge {c χ t Δ : ℝ} {m' : ℕ} {ψ u : ℝ → ℝ} (ht : 1 < t) (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hm' : 2 ≤ m') (hbelow : t ^ 2 ≤ statSq c χ m' - Δ)
    (hE : 0 < energy (aP c χ) ψ u t) :
    c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
        - |wP c χ t| * (aP c χ t / pP t) / 2
      ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t - c * m' := by
  have h := freq_sub_profile_ge (χ := χ) ht hc hχ0 hχc hm' hbelow
  have hr := abs_rate_sub_le (p := pP) (a := aP c χ) (w := wP c χ) (q := qP c χ) (ψ := ψ) (u := u)
    (aP_pos ht (by positivity) hχc) (pP_pos ht) (aP_sq ht (by positivity) hχc) hE
  have := (abs_le.mp hr).1
  linarith

/-- **The rate mismatch above the stationary point**, with the correction of Cvs.Prolate.LiouvilleGreen.PruferRateFrequency subtracted. -/
theorem profile_sub_rate_ge {c χ t Δ : ℝ} {m' : ℕ} {ψ u : ℝ → ℝ} (ht : 1 < t) (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hm' : 2 ≤ m') (habove : statSq c χ m' + Δ ≤ t ^ 2)
    (hE : 0 < energy (aP c χ) ψ u t) :
    c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
        - |wP c χ t| * (aP c χ t / pP t) / 2
      ≤ c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t := by
  have h := profile_sub_freq_ge (χ := χ) ht hc hχ0 hχc hm' habove
  have hr := abs_rate_sub_le (p := pP) (a := aP c χ) (w := wP c χ) (q := qP c χ) (ψ := ψ) (u := u)
    (aP_pos ht (by positivity) hχc) (pP_pos ht) (aP_sq ht (by positivity) hχc) hE
  have := (abs_le.mp hr).2
  linarith

end Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch
