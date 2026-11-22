import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow
import Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
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
# The rate mismatch above the window, in explicit form

Above the stationary point, on `[t₀, q]` with `t₀ > 1` and `t² ≥ θ*² + Δ`, the profile's rate `cm′` exceeds the
rung's by at least `c(m′² − 1)Δ/(2m′(q² − 1)) − (t₀/√(t₀² − 1))(t₀/(t₀² − 1))`, since there `a/p ≤ cm′` bounds the
sum of the two frequencies by `2cm′` and `t² − 1 ≤ q² − 1`: with Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow both `λδ` bounds of the window test of Cvs.Upstream.SecondDerivativeWindowTest
for a `(1, m′)` profile pairing are closed forms.
-/

namespace Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint Cvs.Prolate.LiouvilleGreen.ProfileRateMismatch Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow

/-- **Above the window, explicitly**: on `[t₀, q]` with `t² ≥ θ*² + Δ`,
`cm′ − rate ≥ c(m′² − 1)Δ/(2m′(q² − 1)) − (t₀/√(t₀² − 1))(t₀/(t₀² − 1))`. -/
theorem profile_sub_rate_ge_explicit {c χ t₀ t q Δ : ℝ} {m' : ℕ} {ψ u : ℝ → ℝ} (ht₀ : 1 < t₀) (htt : t₀ ≤ t)
    (htq : t ≤ q) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 2 ≤ m') (hΔ : 0 ≤ Δ)
    (habove : statSq c χ m' + Δ ≤ t ^ 2) (hE : 0 < energy (aP c χ) ψ u t) :
    c * ((m' : ℝ) ^ 2 - 1) * Δ / (2 * m' * (q ^ 2 - 1)) - t₀ / √(t₀ ^ 2 - 1) * (t₀ / (t₀ ^ 2 - 1))
      ≤ c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t := by
  have ht : 1 < t := lt_of_lt_of_le ht₀ htt
  have hm : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
  have hm2 : (0 : ℝ) < (m' : ℝ) ^ 2 - 1 := by nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h2 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < q ^ 2 - 1 := by nlinarith
  have hfreq : 0 < aP c χ t / pP t := div_pos (aP_pos ht hc2 hχc) (pP_pos ht)
  have hcm : 0 < c * m' := by positivity
  -- above the stationary point the frequency is at most `cm′`
  have hle : aP c χ t / pP t ≤ c * m' := by
    have key := freq_sq_sub_profile (χ := χ) ht hc hχ0 hχc hm'
    have hnp : c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (statSq c χ m' - t ^ 2) / (t ^ 2 - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) h2.le
    have hsq : (aP c χ t / pP t) ^ 2 ≤ (c * m') ^ 2 := by linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hcm.le hsq
  have hsum : aP c χ t / pP t + c * m' ≤ 2 * (c * m') := by linarith
  have hden : (t ^ 2 - 1) * (aP c χ t / pP t + c * m') ≤ (q ^ 2 - 1) * (2 * (c * m')) :=
    mul_le_mul (by nlinarith) hsum (by positivity) hq.le
  have hden0 : 0 < (t ^ 2 - 1) * (aP c χ t / pP t + c * m') := by positivity
  have hmain := profile_sub_rate_ge (χ := χ) (ψ := ψ) (u := u) ht hc hχ0 hχc hm' habove hE
  have hcorr := correction_le (χ := χ) ht₀ htt hc hχ0 hχc
  have hfrac : c * ((m' : ℝ) ^ 2 - 1) * Δ / (2 * m' * (q ^ 2 - 1))
      ≤ c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ / ((t ^ 2 - 1) * (aP c χ t / pP t + c * m')) := by
    rw [div_le_div_iff₀ (by positivity) hden0]
    calc c * ((m' : ℝ) ^ 2 - 1) * Δ * ((t ^ 2 - 1) * (aP c χ t / pP t + c * m'))
        ≤ c * ((m' : ℝ) ^ 2 - 1) * Δ * ((q ^ 2 - 1) * (2 * (c * m'))) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ = c ^ 2 * ((m' : ℝ) ^ 2 - 1) * Δ * (2 * m' * (q ^ 2 - 1)) := by ring
  linarith

end Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow
