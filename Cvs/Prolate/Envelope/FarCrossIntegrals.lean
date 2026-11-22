import Mathlib
import Cvs.Prolate.DilateCrossIntegral
import Cvs.Prolate.RadialDilateWronskian

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far cross integrals under `1/ξ` envelopes

If `|ψ(ξ)| ≤ B/ξ` and `|ψ′(ξ)| ≤ D/ξ` for `ξ ≥ 2`, then for `m, n ≥ 2` and `1 ≤ a ≤ b` Cvs.Prolate.DilateCrossIntegral gives
`c²|m² − n²|·|∫_a^b ψ(mθ)ψ(nθ)| ≤ (14/3)BD(1/m + 1/n) + (16/9)|m² − n²||c² − χ|B²/(m³n³)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Envelope.FarCrossIntegrals

open Cvs.Prolate.RadialDilateWronskian (wron)
open Cvs.Prolate.DilateCrossIntegral (tterm kterm)

/-- `∫_a^b θ⁻² ≤ 1` for `1 ≤ a ≤ b`. -/
theorem integral_inv_sq_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ∫ θ in a..b, 1 / θ ^ 2 ≤ 1 := by
  have ha0 : 0 < a := by linarith
  have hd : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ : ℝ => -(1 / θ)) (1 / θ ^ 2) θ := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ
    have hθ0 : θ ≠ 0 := by linarith [hθ.1]
    have h := (hasDerivAt_inv hθ0).neg
    have e : (fun θ : ℝ => -(1 / θ)) = fun θ => -θ⁻¹ := by funext θ; rw [one_div]
    rw [e]
    refine h.congr_deriv ?_
    field_simp
  have hc : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc a b) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hab] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have hb0 : 0 < b := by linarith
  have h1 : 1 / a ≤ 1 := by rw [div_le_one ha0]; exact ha
  have h2 : 0 < 1 / b := by positivity
  linarith

/-- The terms of Cvs.Prolate.DilateCrossIntegral are continuous on `[a, b]` when `ma, na ≥ 2`. -/
theorem continuousOn_terms {ψ v : ℝ → ℝ} {m n a b : ℝ} (hψc : Continuous ψ) (hvcont : Continuous v)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (ha : 1 ≤ a) (hab : a ≤ b) :
    ContinuousOn (tterm ψ v m n) (uIcc a b) ∧ ContinuousOn (kterm ψ m n) (uIcc a b) := by
  have hpm : ∀ θ ∈ uIcc a b, (m * θ) ^ 2 - 1 ≠ 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; exact (Cvs.Prolate.DilateCrossIntegral.sq_sub_one_pos hm (le_trans ha hθ.1)).ne'
  have hpn : ∀ θ ∈ uIcc a b, (n * θ) ^ 2 - 1 ≠ 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; exact (Cvs.Prolate.DilateCrossIntegral.sq_sub_one_pos hn (le_trans ha hθ.1)).ne'
  have cm : Continuous fun θ : ℝ => m * θ := continuous_const.mul continuous_id
  have cn : Continuous fun θ : ℝ => n * θ := continuous_const.mul continuous_id
  have cF : Continuous fun θ => ψ (m * θ) := hψc.comp cm
  have cG : Continuous fun θ => ψ (n * θ) := hψc.comp cn
  have cvm : Continuous fun θ => v (m * θ) := hvcont.comp cm
  have cvn : Continuous fun θ => v (n * θ) := hvcont.comp cn
  have cDm : ContinuousOn (fun θ : ℝ => (m * θ) ^ 2 - 1) (uIcc a b) := ((cm.pow 2).sub continuous_const).continuousOn
  have cDn : ContinuousOn (fun θ : ℝ => (n * θ) ^ 2 - 1) (uIcc a b) := ((cn.pow 2).sub continuous_const).continuousOn
  refine ⟨?_, ?_⟩
  · unfold tterm
    refine (ContinuousOn.div ?_ cDm hpm).neg.add (ContinuousOn.div ?_ cDn hpn)
    · exact (((continuous_const.mul continuous_id).mul cvm).mul cG).continuousOn
    · exact (((continuous_const.mul continuous_id).mul cF).mul cvn).continuousOn
  · unfold kterm
    exact ContinuousOn.div (cF.mul cG).continuousOn (cDm.mul cDn) fun θ hθ => mul_ne_zero (hpm θ hθ) (hpn θ hθ)

/-- **The far cross integral.** -/
theorem abs_integral_le {ψ v v' : ℝ → ℝ} {c χ m n a b B D : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (ha : 1 ≤ a) (hab : a ≤ b) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    c ^ 2 * |m ^ 2 - n ^ 2| * |∫ θ in a..b, ψ (m * θ) * ψ (n * θ)|
      ≤ 14 / 3 * (B * D) * (1 / m + 1 / n) + 16 / 9 * |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * (B ^ 2 / (m ^ 3 * n ^ 3)) := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hmain := Cvs.Prolate.DilateCrossIntegral.abs_integral_le hψ hv hvc hode hm hn ha hab
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  obtain ⟨cT, cK⟩ := continuousOn_terms hψc hvcont hm hn ha hab
  -- pointwise envelopes at the dilates
  have hF : ∀ θ, 1 ≤ θ → |ψ (m * θ)| ≤ B / (m * θ) := fun θ hθ => hψB _ (by nlinarith)
  have hG : ∀ θ, 1 ≤ θ → |ψ (n * θ)| ≤ B / (n * θ) := fun θ hθ => hψB _ (by nlinarith)
  have hFv : ∀ θ, 1 ≤ θ → |v (m * θ)| ≤ D / (m * θ) := fun θ hθ => hvD _ (by nlinarith)
  have hGv : ∀ θ, 1 ≤ θ → |v (n * θ)| ≤ D / (n * θ) := fun θ hθ => hvD _ (by nlinarith)
  -- the Wronskian
  have hW : ∀ θ, 1 ≤ θ → |wron ψ v m n θ| ≤ B * D * (1 / m + 1 / n) := fun θ hθ => by
    have hθ0 : 0 < θ := by linarith
    unfold wron
    have e1 : |m * v (m * θ) * ψ (n * θ)| ≤ m * (D / (m * θ)) * (B / (n * θ)) := by
      rw [abs_mul, abs_mul, abs_of_pos hm0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFv θ hθ) hm0.le) (hG θ hθ) (abs_nonneg _) (by positivity)
    have e2 : |n * ψ (m * θ) * v (n * θ)| ≤ n * (B / (m * θ)) * (D / (n * θ)) := by
      rw [abs_mul, abs_mul, abs_of_pos hn0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF θ hθ) hn0.le) (hGv θ hθ) (abs_nonneg _) (by positivity)
    have hθ2 : 1 ≤ θ ^ 2 := by nlinarith
    have k1 : m * (D / (m * θ)) * (B / (n * θ)) ≤ B * D * (1 / n) := by
      rw [show m * (D / (m * θ)) * (B / (n * θ)) = B * D * (1 / n) / θ ^ 2 by field_simp]
      exact div_le_self (by positivity) hθ2
    have k2 : n * (B / (m * θ)) * (D / (n * θ)) ≤ B * D * (1 / m) := by
      rw [show n * (B / (m * θ)) * (D / (n * θ)) = B * D * (1 / m) / θ ^ 2 by field_simp]
      exact div_le_self (by positivity) hθ2
    have := abs_sub (m * v (m * θ) * ψ (n * θ)) (n * ψ (m * θ) * v (n * θ))
    nlinarith
  -- the first-order terms
  have hT : ∀ θ ∈ Icc a b, |tterm ψ v m n θ| ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := le_trans ha hθ.1
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
  have hK : ∀ θ ∈ Icc a b, |kterm ψ m n θ| ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := le_trans ha hθ.1
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
  have hcont : ContinuousOn (fun θ : ℝ => 1 / θ ^ 2) (uIcc a b) := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun θ hθ => ?_
    rw [uIcc_of_le hab] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])
  have hI1 := integral_inv_sq_le ha hab
  have hI0 : 0 ≤ ∫ θ in a..b, 1 / θ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun θ _ => by positivity
  have hTi : ∫ θ in a..b, |tterm ψ v m n θ| ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab ?_ ((hcont.intervalIntegrable).const_mul
      (8 / 3 * (B * D) * (1 / m + 1 / n))) hT
    · rw [intervalIntegral.integral_const_mul] at h
      have hc0 : 0 ≤ 8 / 3 * (B * D) * (1 / m + 1 / n) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hI1 hc0]
    · exact cT.abs.intervalIntegrable
  have hKi : ∫ θ in a..b, |kterm ψ m n θ| ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab ?_ ((hcont.intervalIntegrable).const_mul
      (16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)))) hK
    · rw [intervalIntegral.integral_const_mul] at h
      have hc0 : 0 ≤ 16 / 9 * (B ^ 2 / (m ^ 3 * n ^ 3)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hI1 hc0]
    · exact cK.abs.intervalIntegrable
  have hWa := hW a ha
  have hWb := hW b (le_trans ha hab)
  have hmn : 0 ≤ |m ^ 2 - n ^ 2| * |c ^ 2 - χ| := by positivity
  have := mul_le_mul_of_nonneg_left hKi hmn
  nlinarith

end Cvs.Prolate.Envelope.FarCrossIntegrals
