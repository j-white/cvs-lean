import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowCosineBessel
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapConnesFromL1
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even Connes part is polynomially large: `‖e‖² ≥ (4/25)‖Ξ(0)‖²/(x log x)`

`StripApproxFromHermite`'s estimate puts `(2/β)·L·a₀` within `o(1)` of `Ξ(0)`, `β = 32b x^{−3/4}`, `|b| ≥ x^{1/4}/20` (Cvs.Approximant.SpineNearQuarticHermite), so
eventually `|L a₀| ≥ (2/5)‖Ξ(0)‖x^{−1/2}`; with `‖e‖² = L·coefficientMass ≥ L a₀²` (Cvs.Route.JointGapConnesFromL1) the bound follows.
-/

noncomputable section

open Real Filter Matrix Topology Set MeasureTheory

namespace Cvs.Approximant.EvenConnesPartLower
open Cvs.ZeroCounting

open Cvs.Route.JointGapConnesFromL1 (connesEven)

/-- **The constant Connes coefficient is polynomially large**: eventually
`(2/5)‖Ξ(0)‖x^{−1/2} ≤ |log x · a₀(x)|`. -/
theorem eventually_coef0_ge :
    ∀ᶠ x : ℝ in atTop, 2 / 5 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ * x ^ (-(1 / 2 : ℝ))
      ≤ |log x * Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0| := by
  let N : ℝ → ℕ := Cvs.Route.JointGapAtConnesVectors.connesThreshold
  let G : ℝ → ℝ → ℝ := fun x => Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1
  let b : ℝ → ℝ := fun x => (Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹
  let β : ℝ → ℝ := fun x => 32*b x*x ^ (-(3/4 : ℝ))
  let err : ℝ → ℝ := fun x =>
    2*√(Cvs.Approximant.StripApproxFromHermite.profileErr x 0 (b x) (G x))+
      2*√(Cvs.Approximant.StripApproxFromHermite.truncErr x 0 (N x))+Cvs.Approximant.StripApproxFromHermite.windowErr x 0
  have hb : ∀ᶠ x : ℝ in atTop, 1/20*x ^ (1/4 : ℝ) ≤ |b x| := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hclose : ∀ᶠ x : ℝ in atTop,
      ∫ u in Icc (0 : ℝ) 1, (G x u-b x*Cvs.Approximant.QuarticHermiteWindowPhi.gH (2*π*x) u)^2
        ≤ 80217/4*x ^ (-(3/2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.integral_spineG_sub_sq_le_rpow hx
  have hNr : ∀ᶠ x : ℝ in atTop, x ^ (1/4 : ℝ) ≤ (N x : ℝ) :=
    Eventually.of_forall fun x => Nat.le_ceil _
  have hp := Cvs.Approximant.StripApproxFromHermite.tendsto_profileErr (a := 0) (by norm_num) G b
    (b₀ := 1/20) (C := 80217/4) (by norm_num) hb hclose
  have ht := Cvs.Approximant.StripApproxFromHermite.tendsto_truncErr (a := 0) (by norm_num) hNr
  have hw := Cvs.Approximant.StripApproxFromHermite.tendsto_windowErr (a := 0) (by norm_num)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h1 := ((continuous_sqrt.tendsto 0).comp hp).const_mul 2
    have h2 := ((continuous_sqrt.tendsto 0).comp ht).const_mul 2
    have h := (h1.add h2).add hw
    simpa only [err, Function.comp_apply, sqrt_zero, mul_zero, add_zero] using h
  have hXi : 0<‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  filter_upwards [herr.eventually (gt_mem_nhds (half_pos hXi)), eventually_ge_atTop (exp 1), hb,
    eventually_ge_atTop 16] with x he hx1 hbx hx16
  have hx0 : 0<x := (exp_pos 1).trans_le hx1
  have hb0 : 0 < |b x| := lt_of_lt_of_le (by positivity) hbx
  have hβ0 : β x ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (abs_pos.mp hb0)) (rpow_pos_of_pos hx0 _).ne'
  have hc : ContinuousOn (G x) (Icc 0 1) :=
    (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hest := Cvs.Approximant.StripApproxFromHermite.norm_two_div_mul_ctransform_sub_Xi_le hx1 rfl hβ0 hc (N x)
      (a := 0) (by norm_num) (z := 0) (by simp)
  have hL : 0<log x := log_pos ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx1)
  change ‖((2 / β x : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (log x) (N x) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x (N x)) 0 - Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖
    ≤ err x at hest
  rw [Cvs.Approximant.ConnesCoefficientsNonvanishing.ctransform_zero_evaluation hL _ _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x (N x)),
    Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none] at hest
  set y := log x * Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0 with hy
  -- `‖Ξ(0)‖ ≤ |2/β||y| + err`
  have hnorm : ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ≤ |2 / β x| * |y| + ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 2 := by
    have h1 := norm_sub_norm_le (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0) (((2 / β x : ℝ) : ℂ) * ((y : ℝ) : ℂ))
    rw [norm_sub_rev] at h1
    have h2 : ‖((2 / β x : ℝ) : ℂ) * ((y : ℝ) : ℂ)‖ = |2 / β x| * |y| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have hβabs : |β x| = 32 * |b x| * x ^ (-(3 / 4 : ℝ)) := by
    simp only [β, abs_mul, abs_of_pos (rpow_pos_of_pos hx0 _)]; norm_num
  have hβge : 8 / 5 * x ^ (-(1 / 2 : ℝ)) ≤ |β x| := by
    rw [hβabs]
    have hr : x ^ (1 / 4 : ℝ) * x ^ (-(3 / 4 : ℝ)) = x ^ (-(1 / 2 : ℝ)) := by
      rw [← rpow_add hx0]; norm_num
    have := mul_le_mul_of_nonneg_right hbx (rpow_pos_of_pos hx0 (-(3 / 4 : ℝ))).le
    nlinarith [rpow_pos_of_pos hx0 (-(1 / 2 : ℝ))]
  have hβpos : 0 < |β x| := abs_pos.mpr hβ0
  have h2β : |2 / β x| = 2 / |β x| := by rw [abs_div]; norm_num
  rw [h2β] at hnorm
  have hy4 : |β x| * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 4 ≤ |y| := by
    have : ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 2 ≤ 2 / |β x| * |y| := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hβpos] at this
    linarith
  calc 2 / 5 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ * x ^ (-(1 / 2 : ℝ)) = (8 / 5 * x ^ (-(1 / 2 : ℝ))) * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 4 := by ring
    _ ≤ |β x| * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 4 := by gcongr
    _ ≤ |y| := hy4

/-- **The even Connes part is polynomially large**: eventually, at every integer `x` with `80 ≤ 2πx`,
`(4/25)‖Ξ(0)‖²/(x log x) ≤ ‖e‖²`. -/
theorem eventually_norm_connesEven_sq_ge :
    ∀ᶠ x : ℕ in atTop, ∀ hx : 80 ≤ 2 * π * x,
      4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / (x * Real.log x) ≤ ‖connesEven hx‖ ^ 2 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_coef0_ge,
    eventually_ge_atTop 3] with x hco hx3 hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL := Real.log_pos hx1
  rw [Cvs.Route.JointGapConnesFromL1.norm_connesEven_sq hx]
  set a₀ := Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0 with ha₀
  have hcoef : Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 = a₀ := by
    rw [← Cvs.Approximant.ConnesResidualFixedScale.connesCoef_none x 0, Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none]
  have hmass : a₀ ^ 2 ≤ Cvs.Approximant.ConnesResidualFixedScale.coefficientMass x := by
    unfold Cvs.Approximant.ConnesResidualFixedScale.coefficientMass
    rw [hcoef]
    have : 0 ≤ (1 / 2 : ℝ) * ∑' k : ℕ, Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k + 1) ^ 2 :=
      mul_nonneg (by norm_num) (tsum_nonneg fun _ => sq_nonneg _)
    linarith
  have hsq : (2 / 5 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ * (x : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (Real.log x * a₀) ^ 2 := by
    rw [← sq_abs (Real.log x * a₀)]
    exact pow_le_pow_left₀ (by positivity) hco 2
  have hr : ((x : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / x := by
    rw [← rpow_natCast, ← rpow_mul hx0.le]; norm_num; exact rpow_neg_one _
  rw [mul_pow, hr, mul_pow] at hsq
  rw [div_le_iff₀ (by positivity)]
  have hfin : Real.log x * a₀ ^ 2 ≤ Real.log x * Cvs.Approximant.ConnesResidualFixedScale.coefficientMass x :=
    mul_le_mul_of_nonneg_left hmass hL.le
  have e1 : (2 / 5) ^ 2 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 * (1 / x) * x = 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 := by
    field_simp; ring
  calc 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 = (2 / 5) ^ 2 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 * (1 / x) * x := e1.symm
    _ ≤ Real.log x ^ 2 * a₀ ^ 2 * x := by
        have := mul_le_mul_of_nonneg_right hsq hx0.le
        rw [mul_pow] at this; exact this
    _ = Real.log x * a₀ ^ 2 * (x * Real.log x) := by ring
    _ ≤ Real.log x * Cvs.Approximant.ConnesResidualFixedScale.coefficientMass x * (x * Real.log x) := by gcongr

end Cvs.Approximant.EvenConnesPartLower
