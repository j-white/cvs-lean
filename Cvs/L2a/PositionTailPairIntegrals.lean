import Mathlib
import Cvs.Prolate.Envelope.FarCrossIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pair integrals of the position-truncated tail, case by case

For a radial solution `ψ` with `|ψ| ≤ B/ξ`, `|ψ′| ≤ D/ξ` on `ξ ≥ 2`, `0 ≤ χ ≤ c²`: the diagonal pairs `a = m ≥ 2` have
`∫_1^b ψ(aθ)² ≤ B²/a²`, and the far pairs `a ≠ m ≥ 2` have
`|∫_1^b ψ(aθ)ψ(mθ)| ≤ (14/3)BD/(c²am|a − m|) + (16/9)B²/(a³m³)` for every `b ≥ 1`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.PositionTailPairIntegrals

/-- **A far diagonal pair**: `∫_1^b ψ(aθ)² ≤ B²/a²` for `a ≥ 2`, `b ≥ 1`. -/
theorem integral_diag_le {ψ : ℝ → ℝ} {B a b : ℝ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hψc : Continuous ψ)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) : ∫ θ in (1 : ℝ)..b, ψ (a * θ) ^ 2 ≤ B ^ 2 / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hpt : ∀ θ ∈ Icc (1 : ℝ) b, ψ (a * θ) ^ 2 ≤ B ^ 2 / a ^ 2 * (1 / θ ^ 2) := fun θ hθ => by
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have h := hψB (a * θ) (by nlinarith [hθ.1])
    have h2 : ψ (a * θ) ^ 2 ≤ (B / (a * θ)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc ψ (a * θ) ^ 2 ≤ (B / (a * θ)) ^ 2 := h2
      _ = B ^ 2 / a ^ 2 * (1 / θ ^ 2) := by field_simp
  have hcont : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc 1 b) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hb] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  have hle := intervalIntegral.integral_mono_on (μ := volume) (f := fun θ => ψ (a * θ) ^ 2) hb
    (((hψc.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable (μ := volume) 1 b)
    ((hcont.intervalIntegrable).const_mul (B ^ 2 / a ^ 2)) hpt
  rw [intervalIntegral.integral_const_mul] at hle
  have hI := Cvs.Prolate.Envelope.FarCrossIntegrals.integral_inv_sq_le le_rfl hb
  have h0 : 0 ≤ B ^ 2 / a ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hI h0]

/-- **A far off-diagonal pair**: `|∫_1^b ψ(aθ)ψ(mθ)| ≤ (14/3)BD/(c²am|a − m|) + (16/9)B²/(a³m³)` for `a ≠ m ≥ 2`. -/
theorem abs_integral_far_le {ψ v v' : ℝ → ℝ} {c χ a m b B D : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (ha : 2 ≤ a) (hm : 2 ≤ m) (ham : a ≠ m) (hb : 1 ≤ b)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    |∫ θ in (1 : ℝ)..b, ψ (a * θ) * ψ (m * θ)|
      ≤ 14 / 3 * (B * D) / (c ^ 2 * (a * m * |a - m|)) + 16 / 9 * (B ^ 2 / (a ^ 3 * m ^ 3)) := by
  have ha0 : 0 < a := by linarith
  have hm0 : 0 < m := by linarith
  have h := Cvs.Prolate.Envelope.FarCrossIntegrals.abs_integral_le hψ hv hvc hode ha hm le_rfl hb hB hD hψB hvD
  have hd : 0 < |a - m| := abs_pos.2 (sub_ne_zero.2 ham)
  have hsq : |a ^ 2 - m ^ 2| = |a - m| * (a + m) := by
    rw [show a ^ 2 - m ^ 2 = (a - m) * (a + m) by ring, abs_mul, abs_of_pos (by linarith : 0 < a + m)]
  have hcc : |c ^ 2 - χ| ≤ c ^ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hden : 0 < c ^ 2 * |a ^ 2 - m ^ 2| := by rw [hsq]; positivity
  have hI : |∫ θ in (1 : ℝ)..b, ψ (a * θ) * ψ (m * θ)|
      ≤ (14 / 3 * (B * D) * (1 / a + 1 / m) + 16 / 9 * |a ^ 2 - m ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (a ^ 3 * m ^ 3)))
        / (c ^ 2 * |a ^ 2 - m ^ 2|) := by
    rw [le_div_iff₀ hden]; linarith
  have e : (14 / 3 * (B * D) * (1 / a + 1 / m) + 16 / 9 * |a ^ 2 - m ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (a ^ 3 * m ^ 3)))
        / (c ^ 2 * |a ^ 2 - m ^ 2|)
      = 14 / 3 * (B * D) / (c ^ 2 * (a * m * |a - m|))
        + 16 / 9 * (|c ^ 2 - χ| / c ^ 2) * (B ^ 2 / (a ^ 3 * m ^ 3)) := by
    rw [hsq]; field_simp; ring
  rw [e] at hI
  have hr : |c ^ 2 - χ| / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; exact hcc
  have h0 : 0 ≤ B ^ 2 / (a ^ 3 * m ^ 3) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hr h0]

end Cvs.L2a.PositionTailPairIntegrals
