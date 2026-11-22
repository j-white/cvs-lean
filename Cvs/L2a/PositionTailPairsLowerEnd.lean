import Mathlib
import Cvs.Prolate.DilateCrossIntegral
import Cvs.Prolate.Envelope.FarCrossIntegrals
import Cvs.Prolate.RadialDilateWronskian

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pair integrals of the position-truncated tail from a lower end `b1 ≥ 1`

For a radial solution `ψ` with `|ψ| ≤ B/ξ`, `|ψ′| ≤ D/ξ` on `ξ ≥ 2`, `0 ≤ χ ≤ c²` and `1 ≤ b1 ≤ b2`:
`∫_{b1}^{b2} ψ(aθ)² ≤ B²/(a²b1)` for `a ≥ 2`, and for `a ≠ m ≥ 2`
`|∫_{b1}^{b2} ψ(aθ)ψ(mθ)| ≤ ((14/3)BD/(c²am|a − m|) + (16/9)B²/(a³m³))/b1`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.PositionTailPairsLowerEnd

open Cvs.Prolate.RadialDilateWronskian (wron)
open Cvs.Prolate.DilateCrossIntegral (tterm kterm)
open Cvs.Prolate.Envelope.FarCrossIntegrals (continuousOn_terms)

/-- `∫_{b1}^{b2} θ⁻² ≤ 1/b1` for `0 < b1 ≤ b2`. -/
theorem integral_inv_sq_le' {b1 b2 : ℝ} (hb1 : 0 < b1) (hb12 : b1 ≤ b2) :
    ∫ θ in b1..b2, 1 / θ ^ 2 ≤ 1 / b1 := by
  have hd : ∀ θ ∈ uIcc b1 b2, HasDerivAt (fun θ : ℝ => -(1 / θ)) (1 / θ ^ 2) θ := fun θ hθ => by
    rw [uIcc_of_le hb12] at hθ
    have hθ0 : θ ≠ 0 := by linarith [hθ.1]
    have h := (hasDerivAt_inv hθ0).neg
    have e : (fun θ : ℝ => -(1 / θ)) = fun θ => -θ⁻¹ := by funext θ; rw [one_div]
    rw [e]
    refine h.congr_deriv ?_
    field_simp
  have hc : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc b1 b2) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hb12] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have h2 : 0 < 1 / b2 := by have : 0 < b2 := by linarith
                             positivity
  linarith

/-- The far cross integral on `[b1, b2]`, with the gain `1/b1`. -/
theorem abs_integral_le_div {ψ v v' : ℝ → ℝ} {c χ m n b1 b2 B D : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hb1 : 1 ≤ b1) (hb12 : b1 ≤ b2) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    c ^ 2 * |m ^ 2 - n ^ 2| * |∫ θ in b1..b2, ψ (m * θ) * ψ (n * θ)|
      ≤ (14 / 3 * (B * D) * (1 / m + 1 / n) + 16 / 9 * |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (m ^ 3 * n ^ 3))) / b1 := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hmain := Cvs.Prolate.DilateCrossIntegral.abs_integral_le hψ hv hvc hode hm hn hb1 hb12
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  obtain ⟨cT, cK⟩ := continuousOn_terms hψc hvcont hm hn hb1 hb12
  -- pointwise envelopes at the dilates
  have hF : ∀ θ, 1 ≤ θ → |ψ (m * θ)| ≤ B / (m * θ) := fun θ hθ => hψB _ (by nlinarith)
  have hG : ∀ θ, 1 ≤ θ → |ψ (n * θ)| ≤ B / (n * θ) := fun θ hθ => hψB _ (by nlinarith)
  have hFv : ∀ θ, 1 ≤ θ → |v (m * θ)| ≤ D / (m * θ) := fun θ hθ => hvD _ (by nlinarith)
  have hGv : ∀ θ, 1 ≤ θ → |v (n * θ)| ≤ D / (n * θ) := fun θ hθ => hvD _ (by nlinarith)
  -- the Wronskian
  have hW : ∀ θ, b1 ≤ θ → |wron ψ v m n θ| ≤ B * D * (1 / m + 1 / n) / b1 := fun θ hθb => by
    have hθ : 1 ≤ θ := le_trans hb1 hθb
    have hθ0 : 0 < θ := by linarith
    unfold wron
    have e1 : |m * v (m * θ) * ψ (n * θ)| ≤ m * (D / (m * θ)) * (B / (n * θ)) := by
      rw [abs_mul, abs_mul, abs_of_pos hm0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFv θ hθ) hm0.le) (hG θ hθ) (abs_nonneg _) (by positivity)
    have e2 : |n * ψ (m * θ) * v (n * θ)| ≤ n * (B / (m * θ)) * (D / (n * θ)) := by
      rw [abs_mul, abs_mul, abs_of_pos hn0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF θ hθ) hn0.le) (hGv θ hθ) (abs_nonneg _) (by positivity)
    have hθ2 : b1 ≤ θ ^ 2 := by nlinarith
    have hb10 : 0 < b1 := by linarith
    have k1 : m * (D / (m * θ)) * (B / (n * θ)) ≤ B * D * (1 / n) / b1 := by
      rw [show m * (D / (m * θ)) * (B / (n * θ)) = B * D * (1 / n) / θ ^ 2 by field_simp]
      exact div_le_div_of_nonneg_left (by positivity) hb10 hθ2
    have k2 : n * (B / (m * θ)) * (D / (n * θ)) ≤ B * D * (1 / m) / b1 := by
      rw [show n * (B / (m * θ)) * (D / (n * θ)) = B * D * (1 / m) / θ ^ 2 by field_simp]
      exact div_le_div_of_nonneg_left (by positivity) hb10 hθ2
    have := abs_sub (m * v (m * θ) * ψ (n * θ)) (n * ψ (m * θ) * v (n * θ))
    have e : B * D * (1 / m + 1 / n) / b1 = B * D * (1 / n) / b1 + B * D * (1 / m) / b1 := by ring
    rw [e]
    nlinarith
  -- the first-order terms
  have hT : ∀ θ ∈ Icc b1 b2, |tterm ψ v m n θ| ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := le_trans hb1 hθ.1
    have hθ0 : 0 < θ := by linarith
    have hmθ : 2 ≤ m * θ := by nlinarith
    have hnθ : 2 ≤ n * θ := by nlinarith
    have hpm : 3 / 4 * (m * θ) ^ 2 ≤ (m * θ) ^ 2 - 1 := by nlinarith
    have hpn : 3 / 4 * (n * θ) ^ 2 ≤ (n * θ) ^ 2 - 1 := by nlinarith
    have hpm0 : 0 < (m * θ) ^ 2 - 1 := by nlinarith
    have hpn0 : 0 < (n * θ) ^ 2 - 1 := by nlinarith
    unfold tterm
    have t1 : |2 * m ^ 3 * θ * v (m * θ) * ψ (n * θ) / ((m * θ) ^ 2 - 1)| ≤ 8 / 3 * (B * D) * (1 / n) * (1 / θ ^ 2) := by
      rw [abs_div, abs_of_pos hpm0, div_le_iff₀ hpm0]
      have h1 : |2 * m ^ 3 * θ * v (m * θ) * ψ (n * θ)| ≤ 2 * m ^ 3 * θ * (D / (m * θ)) * (B / (n * θ)) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * m ^ 3 * θ)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hFv θ hθ1) (by positivity)) (hG θ hθ1) (abs_nonneg _)
          (by positivity)
      have h2 : 2 * m ^ 3 * θ * (D / (m * θ)) * (B / (n * θ)) ≤ 8 / 3 * (B * D) * (1 / n) * (1 / θ ^ 2)
          * ((m * θ) ^ 2 - 1) := by
        have e : 2 * m ^ 3 * θ * (D / (m * θ)) * (B / (n * θ)) = 8 / 3 * (B * D) * (1 / n) * (1 / θ ^ 2)
            * (3 / 4 * (m * θ) ^ 2) / θ := by field_simp; ring
        rw [e]
        have hθ1' : 1 ≤ θ := hθ1
        calc _ ≤ 8 / 3 * (B * D) * (1 / n) * (1 / θ ^ 2) * (3 / 4 * (m * θ) ^ 2) :=
              div_le_self (by positivity) hθ1'
          _ ≤ _ := mul_le_mul_of_nonneg_left hpm (by positivity)
      linarith
    have t2 : |2 * n ^ 3 * θ * ψ (m * θ) * v (n * θ) / ((n * θ) ^ 2 - 1)| ≤ 8 / 3 * (B * D) * (1 / m) * (1 / θ ^ 2) := by
      rw [abs_div, abs_of_pos hpn0, div_le_iff₀ hpn0]
      have h1 : |2 * n ^ 3 * θ * ψ (m * θ) * v (n * θ)| ≤ 2 * n ^ 3 * θ * (B / (m * θ)) * (D / (n * θ)) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * n ^ 3 * θ)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hF θ hθ1) (by positivity)) (hGv θ hθ1) (abs_nonneg _)
          (by positivity)
      have h2 : 2 * n ^ 3 * θ * (B / (m * θ)) * (D / (n * θ)) ≤ 8 / 3 * (B * D) * (1 / m) * (1 / θ ^ 2)
          * ((n * θ) ^ 2 - 1) := by
        have e : 2 * n ^ 3 * θ * (B / (m * θ)) * (D / (n * θ)) = 8 / 3 * (B * D) * (1 / m) * (1 / θ ^ 2)
            * (3 / 4 * (n * θ) ^ 2) / θ := by field_simp; ring
        rw [e]
        have hθ1' : 1 ≤ θ := hθ1
        calc _ ≤ 8 / 3 * (B * D) * (1 / m) * (1 / θ ^ 2) * (3 / 4 * (n * θ) ^ 2) :=
              div_le_self (by positivity) hθ1'
          _ ≤ _ := mul_le_mul_of_nonneg_left hpn (by positivity)
      linarith
    have := abs_add_le (-(2 * m ^ 3 * θ * v (m * θ) * ψ (n * θ) / ((m * θ) ^ 2 - 1)))
      (2 * n ^ 3 * θ * ψ (m * θ) * v (n * θ) / ((n * θ) ^ 2 - 1))
    rw [abs_neg] at this
    nlinarith
  -- the frequency correction
  have hK : ∀ θ ∈ Icc b1 b2, |kterm ψ m n θ| ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := le_trans hb1 hθ.1
    have hθ0 : 0 < θ := by linarith
    have hmθ : 2 ≤ m * θ := by nlinarith
    have hnθ : 2 ≤ n * θ := by nlinarith
    have hpm : 3 / 4 * (m * θ) ^ 2 ≤ (m * θ) ^ 2 - 1 := by nlinarith
    have hpn : 3 / 4 * (n * θ) ^ 2 ≤ (n * θ) ^ 2 - 1 := by nlinarith
    have hP : 0 < ((m * θ) ^ 2 - 1) * ((n * θ) ^ 2 - 1) := by nlinarith
    unfold kterm
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP, abs_mul]
    have h1 : |ψ (m * θ)| * |ψ (n * θ)| ≤ B / (m * θ) * (B / (n * θ)) :=
      mul_le_mul (hF θ hθ1) (hG θ hθ1) (abs_nonneg _) (by positivity)
    have h2 : B / (m * θ) * (B / (n * θ)) ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / θ ^ 2)
        * ((m * θ) ^ 2 - 1) * ((n * θ) ^ 2 - 1) := by
      have e : B / (m * θ) * (B / (n * θ)) = 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / θ ^ 2)
          * ((3 / 4 * (m * θ) ^ 2) * (3 / 4 * (n * θ) ^ 2)) / θ ^ 4 := by field_simp; ring
      rw [e, mul_assoc _ ((m * θ) ^ 2 - 1)]
      have hθ4 : 1 ≤ θ ^ 4 := one_le_pow₀ hθ1
      calc _ ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / θ ^ 2) * ((3 / 4 * (m * θ) ^ 2) * (3 / 4 * (n * θ) ^ 2)) :=
            div_le_self (by positivity) hθ4
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hpm hpn (by positivity) (by nlinarith)) (by positivity)
    linarith
  -- integrate the pointwise bounds
  have hcont : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc b1 b2) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hb12] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  have hb10 : 0 < b1 := by linarith
  have hI1 := integral_inv_sq_le' hb10 hb12
  have hTi : ∫ θ in b1..b2, |tterm ψ v m n θ| ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) * (1 / b1) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hb12 ?_ ((hcont.intervalIntegrable).const_mul
      (8 / 3 * (B * D) * (1 / m + 1 / n))) hT
    · rw [intervalIntegral.integral_const_mul] at h
      have hc0 : 0 ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hI1 hc0]
    · exact cT.abs.intervalIntegrable
  have hKi : ∫ θ in b1..b2, |kterm ψ m n θ| ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / b1) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hb12 ?_ ((hcont.intervalIntegrable).const_mul
      (16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)))) hK
    · rw [intervalIntegral.integral_const_mul] at h
      have hc0 : 0 ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hI1 hc0]
    · exact cK.abs.intervalIntegrable
  have hWa := hW b1 le_rfl
  have hWb := hW b2 hb12
  have hmn : 0 ≤ |m ^ 2 - n ^ 2| * |c ^ 2 - χ| := by positivity
  have := mul_le_mul_of_nonneg_left hKi hmn
  have e : (14 / 3 * (B * D) * (1 / m + 1 / n) + 16 / 9 * |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (m ^ 3 * n ^ 3))) / b1
      = B * D * (1 / m + 1 / n) / b1 + B * D * (1 / m + 1 / n) / b1
        + 8 / 3 * (B * D) * (1 / m + 1 / n) * (1 / b1)
        + |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * (16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / b1)) := by
    field_simp; ring
  rw [e]
  linarith

/-- `∫_{b1}^{b2} ψ(aθ)² ≤ B²/(a²b1)` for `a ≥ 2`, `1 ≤ b1 ≤ b2`. -/
theorem integral_diag_le {ψ : ℝ → ℝ} {B a b1 b2 : ℝ} (ha : 2 ≤ a) (hb1 : 1 ≤ b1) (hb12 : b1 ≤ b2)
    (hψc : Continuous ψ) (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) :
    ∫ θ in b1..b2, ψ (a * θ) ^ 2 ≤ B ^ 2 / (a ^ 2 * b1) := by
  have ha0 : 0 < a := by linarith
  have hb10 : 0 < b1 := by linarith
  have hpt : ∀ θ ∈ Icc b1 b2, ψ (a * θ) ^ 2 ≤ B ^ 2 / a ^ 2 * (1 / θ ^ 2) := fun θ hθ => by
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have h := hψB (a * θ) (by nlinarith [hθ.1])
    have h2 : ψ (a * θ) ^ 2 ≤ (B / (a * θ)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc ψ (a * θ) ^ 2 ≤ (B / (a * θ)) ^ 2 := h2
      _ = B ^ 2 / a ^ 2 * (1 / θ ^ 2) := by field_simp
  have hcont : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc b1 b2) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hb12] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  have hle := intervalIntegral.integral_mono_on (μ := volume) (f := fun θ => ψ (a * θ) ^ 2) hb12
    (((hψc.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable (μ := volume) b1 b2)
    ((hcont.intervalIntegrable).const_mul (B ^ 2 / a ^ 2)) hpt
  rw [intervalIntegral.integral_const_mul] at hle
  have hI := integral_inv_sq_le' hb10 hb12
  have h0 : 0 ≤ B ^ 2 / a ^ 2 := by positivity
  have e : B ^ 2 / (a ^ 2 * b1) = B ^ 2 / a ^ 2 * (1 / b1) := by field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hI h0]

/-- `|∫_{b1}^{b2} ψ(aθ)ψ(mθ)| ≤ ((14/3)BD/(c²am|a − m|) + (16/9)B²/(a³m³))/b1` for `a ≠ m ≥ 2`, `1 ≤ b1 ≤ b2`. -/
theorem abs_integral_far_le {ψ v v' : ℝ → ℝ} {c χ a m b1 b2 B D : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (ha : 2 ≤ a) (hm : 2 ≤ m) (ham : a ≠ m)
    (hb1 : 1 ≤ b1) (hb12 : b1 ≤ b2)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    |∫ θ in b1..b2, ψ (a * θ) * ψ (m * θ)|
      ≤ (14 / 3 * (B * D) / (c ^ 2 * (a * m * |a - m|)) + 16 / 9 * (B ^ 2 / (a ^ 3 * m ^ 3))) / b1 := by
  have ha0 : 0 < a := by linarith
  have hm0 : 0 < m := by linarith
  have hb10 : 0 < b1 := by linarith
  have h := abs_integral_le_div hψ hv hvc hode ha hm hb1 hb12 hB hD hψB hvD
  have hd : 0 < |a - m| := abs_pos.2 (sub_ne_zero.2 ham)
  have hsq : |a ^ 2 - m ^ 2| = |a - m| * (a + m) := by
    rw [show a ^ 2 - m ^ 2 = (a - m) * (a + m) by ring, abs_mul, abs_of_pos (by linarith : 0 < a + m)]
  have hcc : |c ^ 2 - χ| ≤ c ^ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hden : 0 < c ^ 2 * |a ^ 2 - m ^ 2| := by rw [hsq]; positivity
  have hI : |∫ θ in b1..b2, ψ (a * θ) * ψ (m * θ)|
      ≤ (14 / 3 * (B * D) * (1 / a + 1 / m) + 16 / 9 * |a ^ 2 - m ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (a ^ 3 * m ^ 3)))
        / b1 / (c ^ 2 * |a ^ 2 - m ^ 2|) := by
    rw [le_div_iff₀ hden]; linarith
  have e : (14 / 3 * (B * D) * (1 / a + 1 / m) + 16 / 9 * |a ^ 2 - m ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (a ^ 3 * m ^ 3)))
        / b1 / (c ^ 2 * |a ^ 2 - m ^ 2|)
      = (14 / 3 * (B * D) / (c ^ 2 * (a * m * |a - m|))
        + 16 / 9 * (|c ^ 2 - χ| / c ^ 2) * (B ^ 2 / (a ^ 3 * m ^ 3))) / b1 := by
    rw [hsq]; field_simp; ring
  rw [e] at hI
  have hr : |c ^ 2 - χ| / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; exact hcc
  have h0 : 0 ≤ B ^ 2 / (a ^ 3 * m ^ 3) := by positivity
  refine hI.trans (div_le_div_of_nonneg_right ?_ hb10.le)
  nlinarith [mul_le_mul_of_nonneg_right hr h0]

end Cvs.L2a.PositionTailPairsLowerEnd
