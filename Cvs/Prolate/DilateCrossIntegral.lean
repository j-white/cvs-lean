import Mathlib
import Cvs.Prolate.RadialDilateWronskian

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cross integral of two dilates, from their Wronskian

Integrating Cvs.Prolate.RadialDilateWronskian over `[a, b]` with `ma, na ≥ 2`: `c²|m² − n²|·|∫_a^b ψ(mθ)ψ(nθ)|` is at most the Wronskian at both
ends, plus `∫|T|` for the first-order terms `T`, plus `|m² − n²||c² − χ|∫|ψ(mθ)ψ(nθ)|/((m²θ² − 1)(n²θ² − 1))`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.DilateCrossIntegral

open Cvs.Prolate.RadialDilateWronskian (wron)

/-- The first-order terms of `RadialDilateWronskian`'s identity. -/
def tterm (ψ v : ℝ → ℝ) (m n θ : ℝ) : ℝ :=
  -(2 * m ^ 3 * θ * v (m * θ) * ψ (n * θ) / ((m * θ) ^ 2 - 1))
    + 2 * n ^ 3 * θ * ψ (m * θ) * v (n * θ) / ((n * θ) ^ 2 - 1)

/-- The frequency correction of `RadialDilateWronskian`'s identity, without its factor `(c² − χ)(m² − n²)`. -/
def kterm (ψ : ℝ → ℝ) (m n θ : ℝ) : ℝ := ψ (m * θ) * ψ (n * θ) / (((m * θ) ^ 2 - 1) * ((n * θ) ^ 2 - 1))

theorem sq_sub_one_pos {m θ : ℝ} (hm : 2 ≤ m) (hθ : 1 ≤ θ) : 0 < (m * θ) ^ 2 - 1 := by
  have : 2 ≤ m * θ := by nlinarith
  nlinarith

/-- **The cross integral from the Wronskian.** -/
theorem abs_integral_le {ψ v v' : ℝ → ℝ} {c χ m n a b : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (ha : 1 ≤ a) (hab : a ≤ b) :
    c ^ 2 * |m ^ 2 - n ^ 2| * |∫ θ in a..b, ψ (m * θ) * ψ (n * θ)|
      ≤ |wron ψ v m n a| + |wron ψ v m n b| + (∫ θ in a..b, |tterm ψ v m n θ|)
        + |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * ∫ θ in a..b, |kterm ψ m n θ| := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  have hI : ∀ θ ∈ Icc a b, 1 ≤ θ := fun θ hθ => le_trans ha hθ.1
  have hpm : ∀ θ ∈ uIcc a b, (m * θ) ^ 2 - 1 ≠ 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; exact (sq_sub_one_pos hm (hI θ hθ)).ne'
  have hpn : ∀ θ ∈ uIcc a b, (n * θ) ^ 2 - 1 ≠ 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; exact (sq_sub_one_pos hn (hI θ hθ)).ne'
  -- continuity of every term on `[a, b]`
  have cm : Continuous fun θ : ℝ => m * θ := continuous_const.mul continuous_id
  have cn : Continuous fun θ : ℝ => n * θ := continuous_const.mul continuous_id
  have cF : Continuous fun θ => ψ (m * θ) := hψc.comp cm
  have cG : Continuous fun θ => ψ (n * θ) := hψc.comp cn
  have cvm : Continuous fun θ => v (m * θ) := hvcont.comp cm
  have cvn : Continuous fun θ => v (n * θ) := hvcont.comp cn
  have cDm : ContinuousOn (fun θ : ℝ => (m * θ) ^ 2 - 1) (uIcc a b) := ((cm.pow 2).sub continuous_const).continuousOn
  have cDn : ContinuousOn (fun θ : ℝ => (n * θ) ^ 2 - 1) (uIcc a b) := ((cn.pow 2).sub continuous_const).continuousOn
  have cT : ContinuousOn (tterm ψ v m n) (uIcc a b) := by
    unfold tterm
    refine (ContinuousOn.div ?_ cDm hpm).neg.add (ContinuousOn.div ?_ cDn hpn)
    · exact (((continuous_const.mul continuous_id).mul cvm).mul cG).continuousOn
    · exact (((continuous_const.mul continuous_id).mul cF).mul cvn).continuousOn
  have cK : ContinuousOn (kterm ψ m n) (uIcc a b) := by
    unfold kterm
    exact ContinuousOn.div (cF.mul cG).continuousOn (cDm.mul cDn) fun θ hθ => mul_ne_zero (hpm θ hθ) (hpn θ hθ)
  have cW' : Continuous fun θ => m ^ 2 * v' (m * θ) * ψ (n * θ) - n ^ 2 * ψ (m * θ) * v' (n * θ) :=
    ((continuous_const.mul (hvc.comp cm)).mul cG).sub ((continuous_const.mul cF).mul (hvc.comp cn))
  -- integrate the identity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => Cvs.Prolate.RadialDilateWronskian.hasDerivAt_wron (m := m) (n := n) (θ := θ) hψ hv) (cW'.intervalIntegrable a b)
  have hpt : ∀ θ ∈ uIcc a b, c ^ 2 * (m ^ 2 - n ^ 2) * (ψ (m * θ) * ψ (n * θ))
      = -(m ^ 2 * v' (m * θ) * ψ (n * θ) - n ^ 2 * ψ (m * θ) * v' (n * θ))
        + (c ^ 2 - χ) * (m ^ 2 - n ^ 2) * kterm ψ m n θ + tterm ψ v m n θ := fun θ hθ => by
    rw [Cvs.Prolate.RadialDilateWronskian.wron_identity hode (hpm θ hθ) (hpn θ hθ)]
    unfold kterm tterm; ring
  have hint : ∫ θ in a..b, c ^ 2 * (m ^ 2 - n ^ 2) * (ψ (m * θ) * ψ (n * θ))
      = -(wron ψ v m n b - wron ψ v m n a) + (c ^ 2 - χ) * (m ^ 2 - n ^ 2) * (∫ θ in a..b, kterm ψ m n θ)
        + ∫ θ in a..b, tterm ψ v m n θ := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_neg, hFTC, intervalIntegral.integral_const_mul]
    · exact (cW'.intervalIntegrable a b).neg
    · exact (cK.intervalIntegrable).const_mul _
    · exact ((cW'.intervalIntegrable a b).neg).add ((cK.intervalIntegrable).const_mul _)
    · exact cT.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hint
  have e : c ^ 2 * |m ^ 2 - n ^ 2| * |∫ θ in a..b, ψ (m * θ) * ψ (n * θ)|
      = |c ^ 2 * (m ^ 2 - n ^ 2) * ∫ θ in a..b, ψ (m * θ) * ψ (n * θ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c)]
  rw [e, hint]
  have h1 := abs_add_le (-(wron ψ v m n b - wron ψ v m n a) + (c ^ 2 - χ) * (m ^ 2 - n ^ 2) * ∫ θ in a..b, kterm ψ m n θ)
    (∫ θ in a..b, tterm ψ v m n θ)
  have h2 := abs_add_le (-(wron ψ v m n b - wron ψ v m n a)) ((c ^ 2 - χ) * (m ^ 2 - n ^ 2) * ∫ θ in a..b, kterm ψ m n θ)
  have h3 : |-(wron ψ v m n b - wron ψ v m n a)| ≤ |wron ψ v m n a| + |wron ψ v m n b| := by
    rw [abs_neg]; have := abs_sub (wron ψ v m n b) (wron ψ v m n a); linarith
  have h4 : |(c ^ 2 - χ) * (m ^ 2 - n ^ 2) * ∫ θ in a..b, kterm ψ m n θ|
      ≤ |m ^ 2 - n ^ 2| * |c ^ 2 - χ| * ∫ θ in a..b, |kterm ψ m n θ| := by
    rw [abs_mul, abs_mul]
    have := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := kterm ψ m n) hab
    nlinarith [abs_nonneg (c ^ 2 - χ), abs_nonneg (m ^ 2 - n ^ 2),
      mul_nonneg (abs_nonneg (c ^ 2 - χ)) (abs_nonneg (m ^ 2 - n ^ 2))]
  have h5 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := tterm ψ v m n) hab
  linarith

end Cvs.Prolate.DilateCrossIntegral
