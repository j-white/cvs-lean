import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling exponents `W`, `Δ`, `W − 2Δ` and the sharp plunge on a rung

With `Z_T(s) = ∫_s^1 √((u² − T)/(1 − u²)) du` (`ForbiddenZoneGrowth`'s `forbZ 1 T`): `W(T) = Z_T(√T)` is the plunge exponent,
`Δ(T) = ½∫_{√T}^{√3/2} √((u² − T)/(1 − u²)) du` the cell gap at `t = ½`, and `W − 2Δ = Z_T(√3/2)`, which is
antitone in `T` and positive at `T = ¾`. On a rung with `c ≥ 80` and `c² − χ ≥ 5c`,
`1 − λ ≤ (33/40)e⁵·c·(Z + 2)e^{−2Z}` with `Z = Z(√χ/c) = c·W(χ/c²)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.TunnellingExponentSharpPlunge
open Cvs.ZeroCounting

open Cvs.Prolate.ForbiddenZoneGrowth (forbZ PhiC)

/-! ### The exponents -/

/-- The plunge exponent `W(T) = ∫_{√T}^1 √((u² − T)/(1 − u²)) du`. -/
def tunW (T : ℝ) : ℝ := forbZ 1 T √T

/-- The gap margin `W(T) − 2Δ(T) = ∫_{√3/2}^1 √((u² − T)/(1 − u²)) du`. -/
def tunGap (T : ℝ) : ℝ := forbZ 1 T (√3 / 2)

/-- The cell gap `Δ(T) = ½(Z_T(√T) − Z_T(√3/2))`. -/
def tunDelta (T : ℝ) : ℝ := (forbZ 1 T √T - forbZ 1 T (√3 / 2)) / 2

/-- `W = 2Δ + (W − 2Δ)`. -/
theorem tunW_eq (T : ℝ) : tunW T = 2 * tunDelta T + tunGap T := by
  unfold tunW tunDelta tunGap; ring

/-- `W ≥ 0`. -/
theorem tunW_nonneg (T : ℝ) : 0 ≤ tunW T := Cvs.Prolate.ForbiddenZoneGrowth.forbZ_nonneg _ _ _

/-- `√3/2 < 1`. -/
theorem sqrt_three_half_lt_one : √3 / 2 < 1 := by
  have : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **`Δ` in its integral form**: for `T ≤ ¾`, `Δ(T) = ½∫_{√T}^{√3/2} √(u² − T)/√(1 − u²) du`. -/
theorem tunDelta_eq_integral {T : ℝ} (hT : T ≤ 3 / 4) :
    tunDelta T = 1 / 2 * ∫ u in √T..√3 / 2, √(u ^ 2 - T) / √(1 - u ^ 2) := by
  have hs : √T ≤ √3 / 2 := by
    rw [show √3 / 2 = √(3 / 4) by
      rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hsub : uIcc √T (√3 / 2) ⊆ Ioo (-1 : ℝ) 1 := by
    rw [uIcc_of_le hs]
    intro u hu
    exact ⟨by linarith [Real.sqrt_nonneg T, hu.1], lt_of_le_of_lt hu.2 sqrt_three_half_lt_one⟩
  have hq : ∀ u, Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T u = u ^ 2 - T := fun u => by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; ring
  have hderiv : ∀ u ∈ uIcc √T (√3 / 2),
      HasDerivAt (forbZ 1 T) (-(√(u ^ 2 - T) / √(1 - u ^ 2))) u := by
    intro u hu
    have := Cvs.Prolate.ForbiddenZoneGrowth.hasDerivAt_forbZ 1 T (hsub hu)
    rwa [hq] at this
  have hcont : ContinuousOn (fun u => -(√(u ^ 2 - T) / √(1 - u ^ 2))) (uIcc √T (√3 / 2)) := by
    refine ContinuousOn.neg (ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => ?_)
    have h := hsub hu
    exact (Real.sqrt_pos.mpr (by nlinarith [h.1, h.2])).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hFTC
  unfold tunDelta
  linarith

/-- `W − 2Δ` is antitone in `T`. -/
theorem tunGap_anti {T T' : ℝ} (h : T ≤ T') : tunGap T' ≤ tunGap T := by
  unfold tunGap Cvs.Prolate.ForbiddenZoneGrowth.forbZ
  have hb : √(1 - √3 / 2) ∈ Ioo (-√2) (√2) := Cvs.Prolate.ForbiddenZoneGrowth.sqrt_one_sub_mem (by have := Real.sqrt_nonneg 3; linarith)
  refine intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
    (Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 T' hb (Real.sqrt_nonneg _))
    (Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 T hb (Real.sqrt_nonneg _)) fun r _ => ?_
  have hq : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T' (1 - r ^ 2) ≤ Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2) := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; linarith
  gcongr

/-- **The margin is positive at the edge**: `W(¾) − 2Δ(¾) > 0`. -/
theorem tunGap_pos : 0 < tunGap (3 / 4) := by
  have h3 := sqrt_three_half_lt_one
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hb0 : 0 < √(1 - √3 / 2) := Real.sqrt_pos.mpr (by linarith)
  have hb : √(1 - √3 / 2) ∈ Ioo (-√2) (√2) := Cvs.Prolate.ForbiddenZoneGrowth.sqrt_one_sub_mem (by have := Real.sqrt_nonneg 3; linarith)
  unfold tunGap Cvs.Prolate.ForbiddenZoneGrowth.forbZ
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 _ hb hb0.le)
    (fun r hr => ?_) hb0
  have hr2 : r ^ 2 < 1 - √3 / 2 := (Real.lt_sqrt hr.1.le).mp hr.2
  have hu : √3 / 2 < 1 - r ^ 2 := by linarith
  have hu0 : 0 < √3 / 2 := by positivity
  have hq : 0 < Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 (3 / 4) (1 - r ^ 2) := by
    unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP
    have := mul_lt_mul hu hu.le hu0 (by linarith)
    nlinarith
  have h2 : 0 < 2 - r ^ 2 := by nlinarith [sq_nonneg r]
  exact div_pos (mul_pos two_pos (Real.sqrt_pos.mpr hq)) (Real.sqrt_pos.mpr h2)

/-- **Scaling**: `Z_{c, c²T} = c·Z_{1, T}` for `c > 0`. -/
theorem forbZ_scale {c : ℝ} (hc : 0 < c) (T s : ℝ) : forbZ c (c ^ 2 * T) s = c * forbZ 1 T s := by
  unfold Cvs.Prolate.ForbiddenZoneGrowth.forbZ
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hq : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP c (c ^ 2 * T) (1 - r ^ 2) = c ^ 2 * Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2) := by
    unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; ring
  rw [hq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  ring

/-- On a level `χ = c²T`: the forbidden phase at the turning point is `c·W(T)`. -/
theorem forbZ_turning {c χ : ℝ} (hc : 0 < c) : forbZ c χ (√χ / c) = c * tunW (χ / c ^ 2) := by
  have e1 : χ = c ^ 2 * (χ / c ^ 2) := by field_simp
  have e2 : √χ / c = √(χ / c ^ 2) := by
    rw [Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [e2, tunW]
  conv_lhs => rw [e1]
  rw [forbZ_scale hc]
  congr 2
  field_simp

/-! ### The sharp plunge -/

/-- **The plunge with its exact exponent**: for an even rung `g ≢ 0` with `ψ = μg` on `[−1, 1]`, `c ≥ 80`, `χ ≥ 0`
and `c² − χ ≥ 5c`, `1 − λ ≤ (33/40)e⁵·c·(Z + 2)e^{−2Z}`, `λ = (c/2π)μ²`, `Z = Z(√χ/c)`. -/
theorem one_sub_lambda_le_forbZ {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2
      ≤ 33 / 40 * Real.exp 5 * c * (forbZ c χ (√χ / c) + 2) * Real.exp (-(2 * forbZ c χ (√χ / c))) := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  set D := c ^ 2 - χ with hDdef
  have hD0 : 0 < D := by linarith
  set w := (9 * D / (32 * c ^ 4)) ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have hw3 : w ^ 3 = 9 * D / (32 * c ^ 4) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hsχc : √χ ≤ c := by rw [Real.sqrt_le_left hc0.le]; exact hχc.le
  have hsχ0 : 0 ≤ √χ := Real.sqrt_nonneg _
  have hsχ : √χ ^ 2 = χ := Real.sq_sqrt hχ0
  have h1a : D / (2 * c ^ 2) ≤ 1 - √χ / c := by
    have : D = (c - √χ) * (c + √χ) := by rw [hDdef]; nlinarith
    rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, this]
    have e : √χ * (2 * c ^ 2) / c = 2 * c * √χ := by field_simp
    rw [e]; nlinarith [mul_nonneg (sub_nonneg.mpr hsχc) (sub_nonneg.mpr hsχc)]
  have hwle : w ≤ D / (4 * c ^ 2) := by
    apply (pow_le_pow_iff_left₀ hw0.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hw3, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hD2 : 18 * c ^ 2 ≤ D ^ 2 := by nlinarith
    have : 0 ≤ D * c ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : (0 : ℝ) ≤ 9 * D * c ^ 4)]
  have hd1 : w ≤ (1 - √χ / c) / 2 := by
    have : D / (4 * c ^ 2) = D / (2 * c ^ 2) / 2 := by ring
    linarith
  have hdrop : 16 * c ^ 2 * w ^ 3 ≤ 9 * (1 - √χ / c) := by
    rw [hw3]
    have : 16 * c ^ 2 * (9 * D / (32 * c ^ 4)) = 9 * (D / (2 * c ^ 2)) := by field_simp; ring
    rw [this]; linarith
  have hJ := Cvs.Prolate.ForbiddenZoneClosedForm.forbJ_ge_window hc0 hχ0 hχc hw0 hd1 hdrop
  have hK := Cvs.Prolate.ForbiddenZoneClosedForm.ellK_le hc0 hχ0 hχc
  have hP := Cvs.Prolate.PlungeLawIntegral.plunge_P1 hg hg₁ hg₂c hang hc hχ0 hD heven hg0 hμ
  set Z := forbZ c χ (√χ / c) with hZ
  have hZ0 : 0 ≤ Z := Cvs.Prolate.ForbiddenZoneGrowth.forbZ_nonneg _ _ _
  have hΦ := Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_le hZ0
  have hJpos : 0 < Cvs.Prolate.PlungeLawIntegral.forbJ c χ := Cvs.Prolate.PlungeLawIntegral.forbJ_pos hc0 hχc
  have hJinv : 1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ ≤ Real.exp 2 * Real.exp (-(2 * PhiC Z)) / w := by
    rw [div_le_div_iff₀ hJpos hw0, one_mul]
    have h1 : Real.exp 2 * Real.exp (-(2 * PhiC Z)) * Real.exp (2 * PhiC Z - 2) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc w = Real.exp 2 * Real.exp (-(2 * PhiC Z)) * (w * Real.exp (2 * PhiC Z - 2)) := by
          calc w = (Real.exp 2 * Real.exp (-(2 * PhiC Z)) * Real.exp (2 * PhiC Z - 2)) * w := by
                rw [h1, one_mul]
            _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  have hKc : Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D) ≤ c * 3 := by
    have hsD : 20 ≤ √D := by
      rw [Real.le_sqrt (by norm_num) hD0.le]; nlinarith
    have h1 : c / √D * (π / 2) ≤ c * 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_four]
    have h2 : c / (2 * D) ≤ c := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hK0 : 0 ≤ Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D) := by
    unfold Cvs.Prolate.PlungeLawIntegral.ellK
    have : 0 ≤ ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ := setIntegral_nonneg measurableSet_Ioi fun ξ hξ =>
      (one_div_pos.mpr (aP_pos hξ (by positivity) hχc)).le
    positivity
  have hwc : 1 / c ≤ w := by
    apply (pow_le_pow_iff_left₀ (by positivity) hw0.le (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hw3, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hD400 : 400 ≤ D := by nlinarith
    nlinarith [pow_pos hc0 4]
  have hinvw : 1 / w ≤ c := by
    rw [div_le_iff₀ hw0]; rw [div_le_iff₀ hc0] at hwc; linarith
  have hB : 1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ
      ≤ Real.exp 2 * (Real.exp 3 / 2 * (Z + 2) * Real.exp (-(2 * Z))) * c := by
    refine hJinv.trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le) hinvw (by positivity) (by positivity)
  refine hP.trans ?_
  calc 11 / 10 / 2 * (Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D)) / (c * Cvs.Prolate.PlungeLawIntegral.forbJ c χ)
      = 11 / 20 * (Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D)) / c * (1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ) := by
        field_simp; ring
    _ ≤ 11 / 20 * (c * 3) / c * (Real.exp 2 * (Real.exp 3 / 2 * (Z + 2) * Real.exp (-(2 * Z))) * c) :=
        mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKc (by norm_num)) hc0.le) hB
          (by positivity) (by positivity)
    _ = 33 / 40 * Real.exp 5 * c * (Z + 2) * Real.exp (-(2 * Z)) := by
        rw [show Real.exp 5 = Real.exp 2 * Real.exp 3 by rw [← Real.exp_add]; norm_num]
        field_simp; ring

/-- **The sharp plunge on a rung**: for `c ≥ 80` and `c² − χ_k ≥ 5c`, with `T = χ_k/c²`,
`1 − λ_k ≤ (33/40)e⁵·c·(cW(T) + 2)e^{−2cW(T)}`. -/
theorem one_sub_lamR_le_tunW {c : ℝ} {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ)
    (hD : 5 * c ≤ c ^ 2 - lev c k) :
    1 - lamR c k ≤ 33 / 40 * Real.exp 5 * c * (c * tunW (lev c k / c ^ 2) + 2)
      * Real.exp (-(2 * (c * tunW (lev c k / c ^ 2)))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec h
  have hχ0 : 0 ≤ lev c k := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (lev_spec h).1
  have hP := one_sub_lambda_le_forbZ hg hg₁ hg₂c hang hc hχ0 hD heven (rung_ne_zero h) (psi_rung h)
  rw [← mul_comm (muR c k ^ 2), ← Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0, forbZ_turning hc0] at hP
  exact hP

end Cvs.Prolate.TunnellingExponentSharpPlunge
