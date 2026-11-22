import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Prüfer rate against the local frequency

The rate of the Prüfer phase of `(pψ')' + qψ = 0` is the local frequency `√(q/p) = a/p` up to the correction
`w q uψ/(aE)`, and since `2|uψ| ≤ E` that correction is at most `|w| a/(2p)`: `|Θ' − a/p| ≤ |w| (a/p)/2`, so the
phase runs at the frequency `a/p` within the relative error `|w|/2`, which is small beyond the edge.
-/

namespace Cvs.Prolate.LiouvilleGreen.PruferRateFrequency

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Upstream.SturmLiouvillePrufer

/-- **The rate is the frequency `a/p` within relative error `|w|/2`.** -/
theorem abs_rate_sub_le {p a w q ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) (hp : 0 < p t)
    (hapq : a t ^ 2 = p t * q t) (hE : 0 < energy a ψ u t) :
    |rate p a w q ψ u t - a t / p t| ≤ |w t| * (a t / p t) / 2 := by
  unfold rate
  have hq : q t = a t ^ 2 / p t := by
    rw [eq_div_iff hp.ne', hapq]; ring
  have hq0 : 0 < q t := by rw [hq]; positivity
  have hE2 : |u t * ψ t| ≤ energy a ψ u t / 2 := by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
    rw [mul_comm (ψ t)] at this
    linarith
  have key : |w t * q t * (u t * ψ t) / (a t * energy a ψ u t)|
      = |w t| * q t * |u t * ψ t| / (a t * energy a ψ u t) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hq0, abs_of_pos (mul_pos ha hE)]
  rw [add_sub_cancel_left, key]
  have hden : 0 < a t * energy a ψ u t := mul_pos ha hE
  calc |w t| * q t * |u t * ψ t| / (a t * energy a ψ u t)
      ≤ |w t| * q t * (energy a ψ u t / 2) / (a t * energy a ψ u t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = |w t| * (q t / a t) / 2 := by field_simp
    _ = |w t| * (a t / p t) / 2 := by
        rw [hq]; field_simp

end Cvs.Prolate.LiouvilleGreen.PruferRateFrequency
