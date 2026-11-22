import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.L2a.TwoProlateCrossBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The stationary windows of two prolates

`D₂ = (m² − 1/k²) E(χ_a) + p_m (χ_b − χ_a)`. For `km ≥ 2`: past `√S + δ`, `D₂ ≥ (m² − 1/k²) c²t²√S δ` when
`|χ_b − χ_a| ≤ (3/4) m²c²k δ`; on `[k, √S − δ]`, `D₂ ≤ −½(m² − 1/k²) c²t²k δ` when also `χ_a/(c²m²k) ≤ δ` and
`|χ_b − χ_a| ≤ (3/8) m²c²k δ`: half of `StationaryPairMismatchSign`'s margins.
-/

namespace Cvs.L2a.TwoProlateStationaryWindows

open Real Cvs.L2a.NonresonantCrossIntegral Cvs.L2a.StationaryPairMismatchSign Cvs.L2a.TwoProlateCrossBound

theorem Dmr2_eq {c χa χb k m t : ℝ} (hk : k ≠ 0) (hm : m ≠ 0) :
    Dmr2 c χa χb m (1 / k) t = (m ^ 2 - 1 / k ^ 2) * Est c χa k m t + pm m t * (χb - χa) := by
  have h := Dmr_eq_Est (c := c) (χ := χa) (t := t) hk hm
  unfold Dmr at h; unfold Dmr2
  rw [← h]; unfold qm; ring

theorem mk_ge {k m : ℝ} (hk : 0 < k) (hkm : 2 ≤ k * m) : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
  have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- **Right of the window.** -/
theorem D2_right {c χa χb k m t δ : ℝ} (hχa : 0 ≤ χa) (hδ : 0 < δ) (hk : 0 < k) (hm : 0 < m) (hkm : 2 ≤ k * m)
    (hΔ : |χb - χa| ≤ 3 / 4 * m ^ 2 * c ^ 2 * k * δ) (ht : √(k ^ 2 + 1 / m ^ 2) + δ ≤ t) :
    (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * t ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ) ≤ Dmr2 c χa χb m (1 / k) t := by
  rw [Dmr2_eq hk.ne' hm.ne']
  have hE := Est_right (c := c) (χ := χa) (k := k) (m := m) (t := t) hχa hδ hm.ne' ht
  have hmk := mk_ge hk hkm
  have hmk0 : 0 ≤ m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hm2 : 0 ≤ 1 / m ^ 2 := by positivity
  have hkS : k ≤ √(k ^ 2 + 1 / m ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have hp : pm m t ≤ t ^ 2 := Cvs.L2a.StationaryPairElementarySizes.pm_le hm.ne'
  have hp0 : 0 ≤ pm m t := by
    unfold pm; apply div_nonneg _ (by positivity)
    have hsk : k < t := lt_of_lt_of_le (by linarith) ht
    have : 2 ≤ m * t := by nlinarith
    nlinarith
  have hpΔ : -(t ^ 2 * |χb - χa|) ≤ pm m t * (χb - χa) := by
    have := neg_abs_le (χb - χa)
    nlinarith [abs_nonneg (χb - χa)]
  have hbig : t ^ 2 * |χb - χa| ≤ (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * t ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ) := by
    have h1 : t ^ 2 * |χb - χa| ≤ t ^ 2 * (3 / 4 * m ^ 2 * c ^ 2 * k * δ) := mul_le_mul_of_nonneg_left hΔ (sq_nonneg t)
    have h2 : t ^ 2 * (3 / 4 * m ^ 2 * c ^ 2 * k * δ) ≤ (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * t ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ) := by
      have := mul_le_mul hmk hkS hk.le hmk0
      have hc : 0 ≤ c ^ 2 * t ^ 2 * δ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hc]
    linarith
  have hEm := mul_le_mul_of_nonneg_left hE hmk0
  nlinarith

/-- **Left of the window.** -/
theorem D2_left {c χa χb k m t δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hk : 0 < k) (hm : 0 < m) (hkm : 2 ≤ k * m)
    (hδχ : χa / (c ^ 2 * m ^ 2 * k) ≤ δ) (hΔ : |χb - χa| ≤ 3 / 8 * m ^ 2 * c ^ 2 * k * δ)
    (hkt : k ≤ t) (ht : t ≤ √(k ^ 2 + 1 / m ^ 2) - δ) :
    Dmr2 c χa χb m (1 / k) t ≤ -(1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * t ^ 2 * k * δ)) := by
  rw [Dmr2_eq hk.ne' hm.ne']
  have hE := Est_left (c := c) (χ := χa) (k := k) (m := m) (t := t) (δ := δ) hc hk hm.ne' hδ hδχ hkt ht
  have hmk := mk_ge hk hkm
  have hmk0 : 0 ≤ m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hp : pm m t ≤ t ^ 2 := Cvs.L2a.StationaryPairElementarySizes.pm_le hm.ne'
  have hp0 : 0 ≤ pm m t := by
    unfold pm; apply div_nonneg _ (by positivity)
    have : 2 ≤ m * t := by nlinarith
    nlinarith
  have hpΔ : pm m t * (χb - χa) ≤ t ^ 2 * |χb - χa| := by
    have := le_abs_self (χb - χa)
    nlinarith [abs_nonneg (χb - χa)]
  have hsmall : t ^ 2 * |χb - χa| ≤ 1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * t ^ 2 * k * δ) := by
    have h1 : t ^ 2 * |χb - χa| ≤ t ^ 2 * (3 / 8 * m ^ 2 * c ^ 2 * k * δ) := mul_le_mul_of_nonneg_left hΔ (sq_nonneg t)
    have hc0 : 0 ≤ c ^ 2 * t ^ 2 * k * δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmk hc0]
  have hEm := mul_le_mul_of_nonneg_left hE hmk0
  nlinarith

end Cvs.L2a.TwoProlateStationaryWindows
