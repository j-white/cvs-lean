import Mathlib
import Cvs.L2a.PositionTailPairIntegrals
import Cvs.Prolate.EdgeRowShortInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge row of the position-truncated tail

For a radial solution with the far envelopes `B/ξ`, `D/ξ`, `|ψ| ≤ A` and `∫_1^2|ψ′| ≤ A₁` on the edge, `q ≥ κc²ξ²` on
`ξ ≥ 2` and `0 ≤ χ ≤ c²`: for `m ≥ 2` and `X/m ≥ 1`, `|∫_1^{X/m} ψ(θ)ψ(mθ)| ≤ R/m²` with
`R = D(6A/κ + 2A₁/κ + 2A/κ²)/c² + (7/3)BD/c² + B²/18`: the edge part by Cvs.Prolate.EdgeRowShortInterval, the rest as the far pair `(2, 2m)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.PositionTailEdgeRow

/-- The edge-row constant. -/
def rowC (c A A₁ B D κ : ℝ) : ℝ :=
  D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / c ^ 2 + 7 / 3 * (B * D) / c ^ 2 + B ^ 2 / 18

/-- **The edge row**: `|∫_1^b ψ(θ)ψ(mθ)| ≤ rowC/m²` for `m ≥ 2`, `b ≥ 1`. -/
theorem abs_integral_row_le {ψ v v' : ℝ → ℝ} {c χ m b A A₁ B D κ : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hm : 2 ≤ m) (hb : 1 ≤ b) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ A₁) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    |∫ θ in (1 : ℝ)..b, ψ θ * ψ (m * θ)| ≤ rowC c A A₁ B D κ / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, by norm_num⟩)
  have hA₁0 : 0 ≤ A₁ := le_trans (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) hA₁
  set E := D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / c ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  -- the edge part on `[1, b']`, `b' = min b 2`
  have hedge : ∀ b', 1 ≤ b' → b' ≤ 2 → |∫ θ in (1 : ℝ)..b', ψ θ * ψ (m * θ)| ≤ E / m ^ 2 := fun b' h1 h2 => by
    have hA' : ∀ θ ∈ Icc (1 : ℝ) b', |ψ θ| ≤ A := fun θ hθ => hA θ ⟨hθ.1, le_trans hθ.2 h2⟩
    have hA₁' : ∫ θ in (1 : ℝ)..b', |v θ| ≤ A₁ := by
      refine le_trans ?_ hA₁
      exact intervalIntegral.integral_mono_interval le_rfl h1 h2
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hvcont.abs.intervalIntegrable _ _)
    have h := Cvs.Prolate.EdgeRowShortInterval.abs_integral_edge_le hψ hv hode hm h1 h2 hc hκ hκ1 hq hA' hA₁' hvD
    calc _ ≤ D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / (c ^ 2 * m ^ 2) := h
      _ = E / m ^ 2 := by rw [hE]; field_simp
  have hrow0 : 0 ≤ rowC c A A₁ B D κ := by unfold rowC; positivity
  rcases le_or_gt b 2 with hb2 | hb2
  · calc _ ≤ E / m ^ 2 := hedge b hb hb2
      _ ≤ rowC c A A₁ B D κ / m ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          unfold rowC; rw [← hE]; have : 0 ≤ 7 / 3 * (B * D) / c ^ 2 := by positivity
          nlinarith [sq_nonneg B]
  · -- split at `2`
    have hcont : Continuous fun θ => ψ θ * ψ (m * θ) := hψc.mul (hψc.comp (continuous_const.mul continuous_id))
    have hsplit : ∫ θ in (1 : ℝ)..b, ψ θ * ψ (m * θ)
        = (∫ θ in (1 : ℝ)..2, ψ θ * ψ (m * θ)) + ∫ θ in (2 : ℝ)..b, ψ θ * ψ (m * θ) :=
      (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)).symm
    -- the far part as the pair `(2, 2m)` on `[1, b/2]`
    have hscale : ∫ θ in (2 : ℝ)..b, ψ θ * ψ (m * θ)
        = 2 * ∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ ((2 * m) * u) := by
      have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := b / 2)
        (fun θ => ψ θ * ψ (m * θ)) (c := 2) (by norm_num)
      rw [show (2 : ℝ) * 1 = 2 by norm_num, show 2 * (b / 2) = b by ring] at h
      have e : ∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ ((2 * m) * u)
          = ∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ (m * (2 * u)) := by
        congr 1; funext u; ring_nf
      rw [e, h, smul_eq_mul]; ring
    have hfar := Cvs.L2a.PositionTailPairIntegrals.abs_integral_far_le (a := 2) (m := 2 * m) (b := b / 2) hψ hv hvc hode hc
      hχ0 hχ le_rfl (by linarith) (by linarith) (by linarith) hB hD hψB hvD
    have hd : |(2 : ℝ) - 2 * m| = 2 * m - 2 := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd] at hfar
    have hf1 : 14 / 3 * (B * D) / (c ^ 2 * (2 * (2 * m) * (2 * m - 2))) ≤ 7 / 6 * (B * D) / c ^ 2 / m ^ 2 := by
      have hc2 : 0 < c ^ 2 := by positivity
      have hden : c ^ 2 * (4 * m ^ 2) ≤ c ^ 2 * (2 * (2 * m) * (2 * m - 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hc2.le
      calc 14 / 3 * (B * D) / (c ^ 2 * (2 * (2 * m) * (2 * m - 2)))
          ≤ 14 / 3 * (B * D) / (c ^ 2 * (4 * m ^ 2)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 7 / 6 * (B * D) / c ^ 2 / m ^ 2 := by field_simp; ring
    have hf2 : 16 / 9 * (B ^ 2 / ((2 : ℝ) ^ 3 * (2 * m) ^ 3)) ≤ B ^ 2 / 36 / m ^ 2 := by
      rw [div_div, show (16 : ℝ) / 9 * (B ^ 2 / ((2 : ℝ) ^ 3 * (2 * m) ^ 3)) = B ^ 2 / (36 * m ^ 3)
        by field_simp; ring]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have hedge2 := hedge 2 (by norm_num) le_rfl
    rw [hsplit, hscale]
    calc |(∫ θ in (1 : ℝ)..2, ψ θ * ψ (m * θ)) + 2 * ∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ ((2 * m) * u)|
        ≤ |∫ θ in (1 : ℝ)..2, ψ θ * ψ (m * θ)| + 2 * |∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ ((2 * m) * u)| := by
          have := abs_add_le (∫ θ in (1 : ℝ)..2, ψ θ * ψ (m * θ)) (2 * ∫ u in (1 : ℝ)..b / 2, ψ (2 * u) * ψ ((2 * m) * u))
          rw [abs_mul, abs_two] at this; exact this
      _ ≤ E / m ^ 2 + 2 * (7 / 6 * (B * D) / c ^ 2 / m ^ 2 + B ^ 2 / 36 / m ^ 2) := by
          have := hfar.trans (add_le_add hf1 hf2); linarith
      _ = rowC c A A₁ B D κ / m ^ 2 := by unfold rowC; rw [← hE]; field_simp; ring

end Cvs.L2a.PositionTailEdgeRow
